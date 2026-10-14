import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EpsRLX.DeltaData
import Submission.Work.FTS.StrongEps.IsEpsSolPQ.EpsSq_intervalIntegral_le_sqrt
import Submission.Work.FTS.StrongEps.PZeroAux.bumpHkNormBound
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.radialSupMul_cd6
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof
import Submission.Work.FTS.StrongPersist.SP6.WlInf6OfFlatW
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_LocDatum3a.Assembly
import Submission.Work.FTS_RegExport.RXVP.NoHdat.velPkgEasy_noHdat
-- ===== merged: Submission.Work.FTS.EpsEngine.BallLimFam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

open Work.FTS.StrongEps
open Work.FTS.StrongEps.EpsLocalPStar

set_option autoImplicit false

/-- `SmoothOpen` is closed under pointwise negation (used at the `-` of a difference). -/
private theorem smoothOpen_neg_eng {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => -f z θ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen at hf ⊢
  have hfun : Function.uncurry (fun z θ : ℝ => -f z θ)
      = fun p : ℝ × ℝ => -(Function.uncurry f p) := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  exact hf.neg

/-! ## Two elementary `HkMem` transports -/

/-- `HkMem` is invariant under pointwise negation (`HkIntegrand` is). -/
theorem HkMem_neg_open {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hm : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k (fun z θ => -f z θ) := by
  obtain ⟨h1, h2⟩ := hm
  have hpt : ∀ z θ, Work.Spaces.HkIntegrand α k (fun z θ => -f z θ) z θ
      = Work.Spaces.HkIntegrand α k f z θ :=
    fun z θ => congrFun (congrFun (Work.FTS.EllipticEst.HkIntegrand_neg α k f) z) θ
  refine ⟨fun z hz => ?_, ?_⟩
  · rw [show (fun θ => Work.Spaces.HkIntegrand α k (fun z θ => -f z θ) z θ)
        = (fun θ => Work.Spaces.HkIntegrand α k f z θ) from funext (fun θ => hpt z θ)]
    exact h1 z hz
  · rw [show (fun z => ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => -f z θ) z θ)
        = (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) from by
      funext z
      exact MeasureTheory.integral_congr_ae (Eventually.of_forall (fun θ => hpt z θ))]
    exact h2

/-- `EpsMem` only depends on the values of the profile (the squared weighted profile does). -/
theorem EpsMem_congr_pt {α : ℝ} {f g : Fn} (h : ∀ z θ, f z θ = g z θ) (hm : EpsMem α f) :
    EpsMem α g := by
  rw [EpsMem_iff_integrable2] at hm ⊢
  refine hm.congr ?_
  filter_upwards with p
  rw [h p.1 p.2]

/-- `HkMem` only depends on the values of the profile. -/
theorem HkMem_congr_pt {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ, f z θ = g z θ) (hm : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k g := by
  have hfg : f = g := funext (fun z => funext (fun θ => h z θ))
  rw [hfg] at hm
  exact hm

/-! ## The projection-additivity identity -/

/-- **The projection is additive along a difference of two mollified profiles**:
`Pz (J_ε (u − v)) = Pz (J_ε u) − Pz (J_ε v)`, for `u`, `v` smooth on the open quadrant with
ℋ⁴-honesty.  (Equivalently: `Pz (J_ε u) = Pz (J_ε v) + Pz (J_ε (u − v))`.)

The content is the `L₁₂`-additivity `EComparison.L12_sub_HkMem`, which is where the two `HkMem`
hypotheses are used; the rest is linearity of `J_ε` (`EpsRLX.Jeps_sub_eq`) and the pointwise form
of the projection. -/
theorem Pz_Jeps_sub_eq {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {u v : Fn}
    (hρ : IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1) (hε : 0 < ε)
    (hu : Work.FTS.EllipticEst.SmoothOpen u) (hv : Work.FTS.EllipticEst.SmoothOpen v)
    (hmu : Work.Spaces.HkMem α 4 u) (hmv : Work.Spaces.HkMem α 4 v) :
    Pz (Jeps ρ ε (fun z θ => u z θ - v z θ)) = Pz (Jeps ρ ε u) - Pz (Jeps ρ ε v) := by
  have huc : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall u).mp hu
  have hvc : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry v) Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall v).mp hv
  have hJu : Work.FTS.EllipticEst.SmoothOpen (Jeps ρ ε u) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε huc
  have hJv : Work.FTS.EllipticEst.SmoothOpen (Jeps ρ ε v) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε hvc
  have hmu' : Work.Spaces.HkMem α 4 (Jeps ρ ε u) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε huc hmu
  have hmv' : Work.Spaces.HkMem α 4 (Jeps ρ ε v) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε hvc hmv
  have hsub : Jeps ρ ε u - Jeps ρ ε v = Jeps ρ ε (fun z θ => u z θ - v z θ) :=
    Work.FTS.StrongEps.EpsRLX.Jeps_sub_eq hρ.moll hε hu hv
  have hL : Work.Construction.L12 (Jeps ρ ε (fun z θ => u z θ - v z θ)) 0
      = Work.Construction.L12 (Jeps ρ ε u) 0 - Work.Construction.L12 (Jeps ρ ε v) 0 := by
    rw [← hsub]
    exact Work.FTS.StrongEps.EComparison.L12_sub_HkMem hJu hJv hmu' hmv' 0
      (by simp [Work.Spaces.Iz])
  funext z θ
  have hval : Jeps ρ ε (fun z θ => u z θ - v z θ) z θ
      = Jeps ρ ε u z θ - Jeps ρ ε v z θ := by
    have := congrFun (congrFun hsub.symm z) θ
    simpa using this
  simp only [Pi.sub_apply]
  rw [Pz_apply, Pz_apply, Pz_apply, hL, hval]
  ring

/-! ## The ball clause at the limit slice -/

/-- `√(q ^ N) = (√q) ^ N`. -/
private theorem sqrt_pow_eq {q : ℝ} (hq0 : 0 ≤ q) (N : ℕ) :
    Real.sqrt (q ^ N) = (Real.sqrt q) ^ N := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Real.sqrt_mul (pow_nonneg hq0 n), ih, pow_succ]

/-- **The ball clause of `hlimP`**: from the iterate-wise ball bound, the smoothing tail bound, the
open-quadrant smoothness of every slice and the ℋ⁴-honesty of the raw slices, the limit slice
satisfies the same ball bound — with the sharp constant `C₀` (no `√2` loss). -/
theorem Xn_PzJeps_limFam_le {α ε C₀ Cj q : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {F : Fn → Fn} {h₀ : Fn} {τ : ℝ}
    (hρ : IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1) (hε : 0 < ε) (hCj : 0 ≤ Cj)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hxn : ∀ N : ℕ, Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε (slice (iter F h₀ N) τ))) ≤ C₀ * α ^ 2)
    (hbound : ∀ N : ℕ, 1 ≤ N →
      Work.Spaces.HkSq α 4 (Pz (Jeps ρ ε (fun z θ =>
        slice (limFam F h₀) τ z θ - slice (iter F h₀ N) τ z θ))) ≤ Cj * q ^ N)
    (hsmoN : ∀ N : ℕ, Work.FTS.EllipticEst.SmoothOpen (slice (iter F h₀ N) τ))
    (hsmoW : Work.FTS.EllipticEst.SmoothOpen (slice (limFam F h₀) τ))
    (hmemN : ∀ N : ℕ, Work.Spaces.HkMem α 4 (slice (iter F h₀ N) τ))
    (hmemW : Work.Spaces.HkMem α 4 (slice (limFam F h₀) τ)) :
    Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε (slice (limFam F h₀) τ))) ≤ C₀ * α ^ 2 := by
  -- the projection-additivity identity at every iterate
  have hid : ∀ N : ℕ, Pz (Jeps ρ ε (fun z θ =>
      slice (limFam F h₀) τ z θ - slice (iter F h₀ N) τ z θ))
      = Pz (Jeps ρ ε (slice (limFam F h₀) τ)) - Pz (Jeps ρ ε (slice (iter F h₀ N) τ)) :=
    fun N => Pz_Jeps_sub_eq hρ hα hε hsmoW (hsmoN N) hmemW (hmemN N)
  -- the iterate-wise bound, with the tail error
  have key : ∀ N : ℕ, 1 ≤ N →
      Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε (slice (limFam F h₀) τ))) ≤ C₀ * α ^ 2 + Real.sqrt (Cj * q ^ N) := by
    intro N hN
    have hsmA : Work.FTS.EllipticEst.SmoothOpen (Pz (Jeps ρ ε (slice (iter F h₀ N) τ))) :=
      smoothOpen_Pz_of_smoothOpen
        (Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε
          ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hsmoN N)))
    have hsmB : Work.FTS.EllipticEst.SmoothOpen (Pz (Jeps ρ ε (fun z θ =>
        slice (limFam F h₀) τ z θ - slice (iter F h₀ N) τ z θ))) :=
      smoothOpen_Pz_of_smoothOpen
        (Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε
          ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
            (Work.FTS.EllipticEst.smoothOpen_sub hsmoW (hsmoN N))))
    have hmemA : Work.Spaces.HkMem α 4 (Pz (Jeps ρ ε (slice (iter F h₀ N) τ))) :=
      Work.FTS.StrongEps.PZeroAux.PzJepsHkMem 4 hρ hα hε
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hsmoN N)) (hmemN N)
    have hmemDiff : Work.Spaces.HkMem α 4 (fun z θ =>
        slice (limFam F h₀) τ z θ - slice (iter F h₀ N) τ z θ) :=
      HkMem_congr_pt (fun z θ => by
          show slice (limFam F h₀) τ z θ - slice (iter F h₀ N) τ z θ
            = slice (limFam F h₀) τ z θ + -(slice (iter F h₀ N) τ z θ)
          ring)
        (Work.FTS.EllipticEst.HkMem_add_open (α := α) (k := 4) hsmoW
          (smoothOpen_neg_eng (hsmoN N)) hmemW (HkMem_neg_open (hmemN N)))
    have hmemB : Work.Spaces.HkMem α 4 (Pz (Jeps ρ ε (fun z θ =>
        slice (limFam F h₀) τ z θ - slice (iter F h₀ N) τ z θ))) :=
      Work.FTS.StrongEps.PZeroAux.PzJepsHkMem 4 hρ hα hε
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
          (Work.FTS.EllipticEst.smoothOpen_sub hsmoW (hsmoN N))) hmemDiff
    have htri := Work.FTS.StrongEps.EpsE4Thr.HkNorm_triangle α 4
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsmA)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsmB) hmemA hmemB
    -- rewrite the sum as the projected limit slice
    have hsumEq : (fun z θ => Pz (Jeps ρ ε (slice (iter F h₀ N) τ)) z θ
        + Pz (Jeps ρ ε (fun z θ => slice (limFam F h₀) τ z θ
            - slice (iter F h₀ N) τ z θ)) z θ)
        = Pz (Jeps ρ ε (slice (limFam F h₀) τ)) := by
      funext z θ
      have hp := congrFun (congrFun (hid N) z) θ
      rw [hp]
      simp only [Pi.sub_apply]
      ring
    rw [hsumEq] at htri
    have htail : Work.Spaces.HkNorm α 4 (Pz (Jeps ρ ε (fun z θ =>
        slice (limFam F h₀) τ z θ - slice (iter F h₀ N) τ z θ)))
        ≤ Real.sqrt (Cj * q ^ N) := by
      rw [Work.Spaces.HkNorm]
      exact Real.sqrt_le_sqrt (hbound N hN)
    exact htri.trans (add_le_add (hxn N) htail)
  -- pass to the limit in `N`
  have hsqrtq : Real.sqrt q < 1 := by
    nlinarith [Real.sq_sqrt hq0, Real.sqrt_nonneg q]
  have hlim : Filter.Tendsto (fun N : ℕ => C₀ * α ^ 2 + Real.sqrt (Cj * q ^ N))
      Filter.atTop (nhds (C₀ * α ^ 2)) := by
    have h1 : Filter.Tendsto (fun N : ℕ => Real.sqrt (Cj * q ^ N)) Filter.atTop (nhds 0) := by
      have heq : (fun N : ℕ => Real.sqrt (Cj * q ^ N))
          = fun N : ℕ => Real.sqrt Cj * (Real.sqrt q) ^ N := by
        funext N
        rw [Real.sqrt_mul hCj, sqrt_pow_eq hq0 N]
      rw [heq]
      simpa using tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.sqrt_nonneg q) hsqrtq)
    simpa using tendsto_const_nhds.add h1
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    (Filter.eventually_atTop.mpr ⟨1, fun N hN => key N hN⟩)

/-- **The ball clause with the geometric tail supplied**: the `hbound` input of
`Xn_PzJeps_limFam_le` is instantiated by the smoothing estimate `HkSq_JepsPz_le` together with the
tail `EpsSq α (limit − iterate N) ≤ q^N`.  The residual hypotheses are exactly the smoothness and
the ℋ⁴-honesty of the raw slices. -/
theorem Xn_PzJeps_limFam_le_of_tail {α ε C₀ q : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {F : Fn → Fn} {h₀ : Fn} {τ : ℝ}
    (hρ : IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hxn : ∀ N : ℕ, Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε (slice (iter F h₀ N) τ))) ≤ C₀ * α ^ 2)
    (htail : ∀ N : ℕ, 1 ≤ N →
      EpsMem α (fun z θ => slice (limFam F h₀) τ z θ - slice (iter F h₀ N) τ z θ) ∧
      EpsSq α (fun z θ => slice (limFam F h₀) τ z θ - slice (iter F h₀ N) τ z θ) ≤ q ^ N)
    (hsmoN : ∀ N : ℕ, Work.FTS.EllipticEst.SmoothOpen (slice (iter F h₀ N) τ))
    (hsmoW : Work.FTS.EllipticEst.SmoothOpen (slice (limFam F h₀) τ))
    (hmemN : ∀ N : ℕ, Work.Spaces.HkMem α 4 (slice (iter F h₀ N) τ))
    (hmemW : Work.Spaces.HkMem α 4 (slice (limFam F h₀) τ)) :
    Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε (slice (limFam F h₀) τ))) ≤ C₀ * α ^ 2 := by
  obtain ⟨D, hDpos, hD⟩ := Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le ρ hρ
  refine Xn_PzJeps_limFam_le (Cj := D * (D / ε) ^ (2 * 4)) (Φs := Φs) (E := E)
    (F := F) (h₀ := h₀) (τ := τ) hρ hα hε ?_ hq0 hq1 hxn ?_ hsmoN hsmoW hmemN hmemW
  · positivity
  · intro N hN
    have hb := hD α hα ε hε hε1 4 (by norm_num)
      (fun z θ => slice (limFam F h₀) τ z θ - slice (iter F h₀ N) τ z θ)
      (Work.FTS.EllipticEst.smoothOpen_sub hsmoW (hsmoN N))
      (htail N hN).1
    exact hb.trans (mul_le_mul_of_nonneg_left (htail N hN).2
      (mul_nonneg hDpos.le (pow_nonneg (div_nonneg hDpos.le hε.le) _)))


/-! ## The one-step transfer of the class ball

Both the invariant clause (`hkeepIter`) and the limit clause (`hlimP`) of the local step need the
*same* estimate: the projected-mollified class ball of a profile is bounded by that of a nearby
profile plus the (smoothing-priced) size of the difference.  We isolate it here. -/

/-- **The one-step transfer of the class ball.**  For `u`, `v` smooth on the open quadrant with
ℋ⁴-honesty,

  `Xn α (Pz (J_ε u)) ≤ Xn α (Pz (J_ε v)) + √(HkSq α 4 (Pz (J_ε (u − v))))`,

with the sharp constant `1` on the class-ball term (the sharp triangle inequality
`EpsE4Thr.HkNorm_triangle` and the projection-additivity identity `Pz_Jeps_sub_eq`).

The statement is *exactly* what the two ball clauses of the local step consume:

* `hkeepIter`: `v := h₀` (the datum, whose class ball is the invariant's initial bound) and
  `u := slice (iter (n+1)) τ`;
* `hlimP`: `v := slice (iter N) τ`, `u := slice (limFam …) τ`, with the tail bound on the
  difference and a passage to the limit in `N` (`Xn_PzJeps_limFam_le_of_tail`). -/
theorem Xn_PzJeps_sub_le {α ε Cb : ℝ} {ρ : ℝ × ℝ → ℝ} {u v : Fn}
    (hρ : IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1) (hε : 0 < ε)
    (hsmu : Work.FTS.EllipticEst.SmoothOpen u) (hsmv : Work.FTS.EllipticEst.SmoothOpen v)
    (hmu : Work.Spaces.HkMem α 4 u) (hmv : Work.Spaces.HkMem α 4 v)
    (hb : Work.Spaces.HkSq α 4 (Pz (Jeps ρ ε (fun z θ => u z θ - v z θ))) ≤ Cb) :
    Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε u))
      ≤ Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε v)) + Real.sqrt Cb := by
  have hid := Pz_Jeps_sub_eq hρ hα hε hsmu hsmv hmu hmv
  have hsmA : Work.FTS.EllipticEst.SmoothOpen (Pz (Jeps ρ ε v)) :=
    smoothOpen_Pz_of_smoothOpen
      (Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsmv))
  have hsmB : Work.FTS.EllipticEst.SmoothOpen (Pz (Jeps ρ ε (fun z θ => u z θ - v z θ))) :=
    smoothOpen_Pz_of_smoothOpen
      (Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
          (Work.FTS.EllipticEst.smoothOpen_sub hsmu hsmv)))
  have hmemA : Work.Spaces.HkMem α 4 (Pz (Jeps ρ ε v)) :=
    Work.FTS.StrongEps.PZeroAux.PzJepsHkMem 4 hρ hα hε
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsmv) hmv
  have hmemDiff : Work.Spaces.HkMem α 4 (fun z θ => u z θ - v z θ) :=
    HkMem_congr_pt (fun z θ => by
        show u z θ - v z θ = u z θ + -(v z θ)
        ring)
      (Work.FTS.EllipticEst.HkMem_add_open (α := α) (k := 4) hsmu
        (smoothOpen_neg_eng hsmv) hmu (HkMem_neg_open hmv))
  have hmemB : Work.Spaces.HkMem α 4 (Pz (Jeps ρ ε (fun z θ => u z θ - v z θ))) :=
    Work.FTS.StrongEps.PZeroAux.PzJepsHkMem 4 hρ hα hε
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
        (Work.FTS.EllipticEst.smoothOpen_sub hsmu hsmv)) hmemDiff
  have htri := Work.FTS.StrongEps.EpsE4Thr.HkNorm_triangle α 4
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsmA)
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsmB) hmemA hmemB
  have hsumEq : (fun z θ => Pz (Jeps ρ ε v) z θ
      + Pz (Jeps ρ ε (fun z θ => u z θ - v z θ)) z θ)
      = Pz (Jeps ρ ε u) := by
    funext z θ
    have hp := congrFun (congrFun hid z) θ
    rw [hp]
    simp only [Pi.sub_apply]
    ring
  rw [hsumEq] at htri
  have htail : Work.Spaces.HkNorm α 4 (Pz (Jeps ρ ε (fun z θ => u z θ - v z θ)))
      ≤ Real.sqrt Cb := by
    rw [Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt hb
  exact htri.trans (add_le_add le_rfl htail)

/-- **The one-step transfer in the scheme's energy**: the smoothing estimate
`EpsSqTools.HkSq_JepsPz_le` prices the difference term, so the residual hypothesis is the single
`EpsMem` of the difference. -/
theorem exists_Xn_PzJeps_sub_le_sqrt_EpsSq (ρ : ℝ × ℝ → ℝ)
    (hρ : IsSmoothKernel ρ) :
    ∃ D : ℝ, 0 < D ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ u v : Fn,
        Work.FTS.EllipticEst.SmoothOpen u → Work.FTS.EllipticEst.SmoothOpen v →
        Work.Spaces.HkMem α 4 u → Work.Spaces.HkMem α 4 v →
        EpsMem α (fun z θ => u z θ - v z θ) →
        Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε u))
          ≤ Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε v))
            + Real.sqrt (D * (D / ε) ^ (2 * 4)
                * EpsSq α (fun z θ => u z θ - v z θ)) := by
  obtain ⟨D, hDpos, hD⟩ := Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le ρ hρ
  refine ⟨D, hDpos, ?_⟩
  intro α hα ε hε hε1 u v hsmu hsmv hmu hmv hme
  refine Xn_PzJeps_sub_le hρ hα hε hsmu hsmv hmu hmv ?_
  exact hD α hα ε hε hε1 4 (by norm_num) (fun z θ => u z θ - v z θ)
    (Work.FTS.EllipticEst.smoothOpen_sub hsmu hsmv) hme


/-! ## The `hkeepIter` ball clause

The invariant clause of the local step is `Xn α (Pz (J_ε (slice (iter (n+1)) τ))) ≤ C₀ α²` from the
*same* datum bound `Xn α (Pz (J_ε h₀)) ≤ C₀ α²` (`iter_succ` makes each iterate the datum plus an
interval integral), so it is an instance of the one-step transfer with `v := h₀`.  The difference is
the Picard increment `∫₀^τ F (slice (iter n) s) ds`, whose `EpsSq`-size is `≤ τ * (τ * B)` by
`VolterraAux.EpsMem_and_EpsSq_intervalIntegral_le`, and the smoothing estimate `hgate` (an instance
of `EpsSqTools.HkSq_JepsPz_le`) prices it. -/

end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.LocalStepXBall =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

open Work.FTS.StrongEps

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The `X`-ball invariant of the local step** (`Xn α = HkNorm α 4`): open-quadrant smoothness,
honesty and `EpsSq`-size of the profile, and the class-`C` data and ball clause of its *projected
mollified* image. -/
def XBall (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε R C₀ : ℝ) (u : Fn) : Prop :=
  Work.FTS.EllipticEst.SmoothOpen u ∧ EpsMem α u ∧ EpsSq α u ≤ R ∧
    Work.FTS.ClassC.ClassC α (Pz (Jeps ρ ε u)) ∧ Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε u))
      ≤ C₀ * α ^ 2

theorem XBall.smoothOpen {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε R C₀ : ℝ} {u : Fn}
    (h : XBall α ρ ε R C₀ u) : Work.FTS.EllipticEst.SmoothOpen u := h.1

theorem XBall.mem {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε R C₀ : ℝ} {u : Fn}
    (h : XBall α ρ ε R C₀ u) : EpsMem α u := h.2.1

theorem XBall.sq_le {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε R C₀ : ℝ} {u : Fn}
    (h : XBall α ρ ε R C₀ u) : EpsSq α u ≤ R := h.2.2.1

theorem XBall.classC {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε R C₀ : ℝ} {u : Fn}
    (h : XBall α ρ ε R C₀ u) : Work.FTS.ClassC.ClassC α (Pz (Jeps ρ ε u)) := h.2.2.2.1

theorem XBall.ball {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε R C₀ : ℝ} {u : Fn}
    (h : XBall α ρ ε R C₀ u) : Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε u)) ≤ C₀ * α ^ 2 := h.2.2.2.2

/-- **`Feps u` is `C^∞` on the open quadrant as soon as `ClassC α (Pz (J_ε u))` holds** — the
class-`C` clause alone (no `ℋ⁶`-size and no `SmoothOpen u`). -/
theorem smoothOpen_Feps_of_classC {α Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {ε : ℝ} {u : Fn}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ) (hε : 0 < ε)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hu : Work.FTS.ClassC.ClassC α (Pz (Jeps ρ ε u))) :
    Work.FTS.EllipticEst.SmoothOpen (Feps α ρ ε Φs E u) := by
  have hRHS : Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E (Pz (Jeps ρ ε u))) :=
    smoothOpen_profRHS_of_classC hα hEll hstar hu
  have hJ : Work.FTS.EllipticEst.SmoothOpen
      (Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E (Pz (Jeps ρ ε u)))) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hRHS)
  exact smoothOpen_Pz_of_smoothOpen hJ

/-- **`Feps` vanishes off the open quadrant, unconditionally in the profile** (both `J_ε` and the
projection's correction profile `bump` are supported in `Q0`). -/
theorem Feps_eq_zero_off_Q0 (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn) (w : Fn)
    (q : ℝ × ℝ) (hq : q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :
    Feps α ρ ε Φs E w q.1 q.2 = 0 := by
  have hq' : ¬(0 < q.1 ∧ q.2 ∈ Set.Ioo 0 (Real.pi / 2)) := fun h => hq ⟨h.1, h.2⟩
  have hbump0 : bump q.1 q.2 = 0 := by
    rw [bump_eq_zero_iff]
    by_cases h1 : 0 < q.1
    · by_cases h2 : q.2 ∈ Set.Ioo 0 (Real.pi / 2)
      · exact absurd ⟨h1, h2⟩ hq'
      · rw [Set.mem_Ioo, not_and_or] at h2
        rcases h2 with h2 | h2
        · exact Or.inr (Or.inr (Or.inl (by linarith [Real.pi_pos])))
        · exact Or.inr (Or.inr (Or.inr (by linarith [Real.pi_pos])))
    · exact Or.inl (by linarith)
  show Pz (Jeps ρ ε (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E
    (Pz (Jeps ρ ε w)))) q.1 q.2 = 0
  rw [Pz_apply, Jeps_eq_zero ρ ε _ hq', hbump0]
  ring

/-- **The engine's per-profile inputs at the `X`-ball**: continuity of `Feps u` on the open quadrant
and vanishing off it, for `u ∈ XBall`. -/
theorem continuousOn_Feps_of_XBall {α Ce Cs R C₀ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {ε : ℝ} {u : Fn}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ) (hε : 0 < ε)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hu : XBall α ρ ε R C₀ u) :
    ContinuousOn (fun q : ℝ × ℝ => Feps α ρ ε Φs E u q.1 q.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) ∧
      (∀ q : ℝ × ℝ, q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) →
        Feps α ρ ε Φs E u q.1 q.2 = 0) := by
  have hsmo := smoothOpen_Feps_of_classC (α := α) (Ce := Ce) (Cs := Cs) (ρ := ρ) (Φs := Φs)
    (E := E) (ε := ε) (u := u) hα hρ hε hEll hstar hu.classC
  refine ⟨?_, fun q hq => Feps_eq_zero_off_Q0 α ρ ε Φs E u q hq⟩
  exact (hsmo.forall 0).continuousOn



end Work.FTS.EpsEngine
end
end
