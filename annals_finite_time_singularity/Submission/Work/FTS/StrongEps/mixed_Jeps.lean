import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.RPFresh.straight_transfers
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgEngine
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
import Submission.Work.FTS.OpenPkg.Pieces4
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EpsE4Thr.JepsJoint.Jeps_fam_continuous
import Submission.Work.FTS.StrongEps.JepsHkMem.continuousOn_Jeps
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.PthIter2VftsAux =====
section

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





end Work.FTS.EllipticEst.Cores.AlphaRateEstEllT
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.Rl1.L12densIntegralLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.Rl1

open MeasureTheory Set
open scoped Real


end Work.FTS.Nonlinear.Pieces.Rl1
end
-- ===== merged: Submission.Work.FTS.StrongEps.mixed_Jeps =====
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

open Work.FTS.Galerkin (Fn)

set_option maxHeartbeats 1000000

/-! ## `C^∞`-smoothness on the open quadrant, and its closure under the two operators -/

/-- `C^∞`-smoothness of a profile on the open quadrant `Quad = (0,∞) × (0,π/2)`.
(The order `∞` is the genuine smooth order `Work.Stability.smoothOrder`, *not* the analytic
order `⊤` of this Mathlib.) -/
def SmQ (g : ℝ → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) Quad

/-- The hypothesis `∀ n, ContDiffOn ℝ n f Quad` of the target is `C^∞`-smoothness on the open
quadrant (`ContDiffOn` at every *finite* order is the smooth order). -/
theorem smQ_of_forall_nat {g : ℝ → ℝ → ℝ}
    (h : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Quad) : SmQ g :=
  contDiffOn_infty.mpr h

namespace SmQ

theorem pth {g : ℝ → ℝ → ℝ} (h : SmQ g) : SmQ (Work.Spaces.pth g) :=
  Work.FTS.LocData.contDiffOn_pth isOpen_Quad h

theorem pz {g : ℝ → ℝ → ℝ} (h : SmQ g) : SmQ (Work.Spaces.pz g) :=
  Work.FTS.LocData.contDiffOn_pz isOpen_Quad h

theorem DthIter {g : ℝ → ℝ → ℝ} (h : SmQ g) (i : ℕ) : SmQ (Work.Spaces.DthIter i g) :=
  Work.FTS.LocData.contDiffOn_DthIter isOpen_Quad h i

theorem DzIter {g : ℝ → ℝ → ℝ} (h : SmQ g) (j : ℕ) : SmQ (Work.Spaces.DzIter j g) :=
  Work.FTS.LocData.contDiffOn_DzIter isOpen_Quad h j

/-- `C^∞` on an open set gives `C¹`. -/
theorem one {g : ℝ → ℝ → ℝ} (h : SmQ g) : ContDiffOn ℝ 1 (Function.uncurry g) Quad :=
  h.of_le (by simp)

end SmQ

/-! ## The two inductions -/

/-- **`D_θ^i` commutes with `J_ε`** on the open quadrant. -/
theorem DthIter_mixed_Jeps (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ → ℝ} (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (Jeps ρ ε f)))
      (Function.uncurry (Jeps ρ ε (Work.Spaces.DthIter i f))) Quad := by
  induction i with
  | zero => intro p hp; rfl
  | succ i ih =>
    -- the two functions agree on `Quad`, so `D_θ` of them agrees on `Quad`
    have hcongr := Work.FTS.TransportS.Dth_congrOn isOpen_Quad ih
    -- `D_θ^i f` is smooth on `Quad`, hence `Dth_Jeps` applies to it
    have hsm : SmQ (Work.Spaces.DthIter i f) := (smQ_of_forall_nat hf).DthIter i
    have hpth : SmQ (Work.Spaces.pth (Work.Spaces.DthIter i f)) :=
      Work.FTS.LocData.contDiffOn_pth isOpen_Quad hsm
    intro p hp
    have hz : 0 < p.1 := hp.1
    have hθ : p.2 ∈ Set.Ioo 0 (π / 2) := hp.2
    have h1 : Work.Spaces.Dth (Work.Spaces.DthIter i (Jeps ρ ε f)) p.1 p.2
        = Work.Spaces.Dth (Jeps ρ ε (Work.Spaces.DthIter i f)) p.1 p.2 := hcongr hp
    have h2 : Work.Spaces.Dth (Jeps ρ ε (Work.Spaces.DthIter i f)) p.1 p.2
        = Jeps ρ ε (Work.Spaces.Dth (Work.Spaces.DthIter i f)) p.1 p.2 :=
      Dth_Jeps ρ hρ hε (hsm.one) hpth.continuousOn hz hθ
    change Work.Spaces.DthIter (i + 1) (Jeps ρ ε f) p.1 p.2
        = Jeps ρ ε (Work.Spaces.DthIter (i + 1) f) p.1 p.2
    rw [Work.Spaces.DthIter_succ, h1, h2, Work.Spaces.DthIter_succ]

/-- **`D_z^j` commutes with `J_ε`** on the open quadrant, for any profile `g` smooth there. -/
theorem DzIter_Jeps_of_smooth (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {g : ℝ → ℝ → ℝ} (hg : SmQ g) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j (Jeps ρ ε g)))
      (Function.uncurry (Jeps ρ ε (Work.Spaces.DzIter j g))) Quad := by
  induction j with
  | zero => intro p hp; rfl
  | succ j ih =>
    have hcongr := Work.FTS.TransportS.Dz_congrOn isOpen_Quad ih
    have hsm : SmQ (Work.Spaces.DzIter j g) := hg.DzIter j
    have hpz : SmQ (Work.Spaces.pz (Work.Spaces.DzIter j g)) := hsm.pz
    intro p hp
    have hz : 0 < p.1 := hp.1
    have hθ : p.2 ∈ Set.Ioo 0 (π / 2) := hp.2
    have h1 : Work.Spaces.Dz (Work.Spaces.DzIter j (Jeps ρ ε g)) p.1 p.2
        = Work.Spaces.Dz (Jeps ρ ε (Work.Spaces.DzIter j g)) p.1 p.2 := hcongr hp
    have h2 : Work.Spaces.Dz (Jeps ρ ε (Work.Spaces.DzIter j g)) p.1 p.2
        = Jeps ρ ε (Work.Spaces.Dz (Work.Spaces.DzIter j g)) p.1 p.2 :=
      Dz_Jeps hρ hε hsm.one hpz.continuousOn hz hθ
    change Work.Spaces.DzIter (j + 1) (Jeps ρ ε g) p.1 p.2
        = Jeps ρ ε (Work.Spaces.DzIter (j + 1) g) p.1 p.2
    rw [Work.Spaces.DzIter_succ, h1, h2, Work.Spaces.DzIter_succ]

/-! ## The target -/

/-- **`E1`, iterated form: `D_z^j D_θ^i (J_ε f) = J_ε (D_z^j D_θ^i f)` on the open quadrant**,
for a profile `f` which is `C^n` there for every `n`. -/
theorem mixed_Jeps (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ → ℝ} (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (j i : ℕ) :
    Work.Spaces.mixed j i (Jeps ρ ε f) z θ = Jeps ρ ε (Work.Spaces.mixed j i f) z θ := by
  have hp : (z, θ) ∈ Quad := ⟨hz, hθ⟩
  -- push the `j` outer `D_z`-derivatives through the equality `D_θ^i (J_ε f) = J_ε (D_θ^i f)`
  have h1 : Set.EqOn
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.DthIter i (Jeps ρ ε f))))
      (Function.uncurry (Work.Spaces.DzIter j (Jeps ρ ε (Work.Spaces.DthIter i f)))) Quad :=
    Work.FTS.TransportS.DzIter_congrOn isOpen_Quad (DthIter_mixed_Jeps ρ hρ hε hf i) j
  -- then commute the `D_z`-iterates with `J_ε` for the smooth profile `D_θ^i f`
  have h2 := DzIter_Jeps_of_smooth ρ hρ hε ((smQ_of_forall_nat hf).DthIter i) j
  exact (h1 hp).trans (h2 hp)

end Work.FTS.StrongEps
end
end
