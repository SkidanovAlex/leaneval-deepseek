/-
Copyright: work module for the Elginda finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/BallLimFam.lean`

**The ball clause of `hlimP`, reduced to a single named interface item.**

The `X`-ball invariant of the local step carries `Xn α (Pz (J_ε (slice (iter F h₀ N) τ))) ≤ C₀ α²`
(`Xn = HkNorm α 4`) for every Picard iterate, and `hlimP` asks for the same bound at the limit
slice.  This file proves that reduction, with the *sharp* triangle inequality
(`EpsE4Thr.HkNorm_triangle`), from

1. the **projection-additivity identity**
   `Pz (J_ε u) = Pz (J_ε v) + Pz (J_ε (u − v))` for `u v` smooth on the open quadrant with
   `HkMem α 4` (proved here as `Pz_Jeps_sub_eq`) — the `L₁₂`-additivity it needs is
   `EComparison.L12_sub_HkMem`, whose `HkMem α 4` hypotheses are what makes this an *interface
   item* rather than a free identity;
2. the **smoothing tail bound** `HkSq α 4 (Pz (J_ε (u − v))) ≤ Cj q^N`, an explicit hypothesis here
   (instantiable by `EpsSqTools.HkSq_JepsPz_le` fed with the geometric tail
   `EpsSq α (iterate N − limit) ≤ q^N` of `EpsSq_iter_limFam_le`).

The residual hypotheses are therefore

* `hmemN`, `hmemW` — `HkMem α 4` of the **raw slices**, uniformly in the iterate index and at the
  limit.  This is the *one* missing interface item of the ball clause: the `X`-ball carries
  `EpsMem` (an a.e. `L²` statement) but no ℋ⁴-honesty of the raw profiles — the same
  one-derivative-per-application wall that the class-`C` propagation meets.
* `hbound` — the tail, instantiable (see the module docstring of `HkSq_JepsPz_le`).

Everything is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.HkNorm_triangle
import Submission.Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EpsRLX.DeltaData
import Submission.Work.FTS.StrongEps.HkMem_Jeps
import Submission.Work.FTS.StrongEps.PZeroAux.PzJepsHkMem
import Submission.Work.FTS.EpsEngine.SmoothOpenFeps
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.GalFields.Tail.SlotAdjoints
import Submission.Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.Iter

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
theorem Xn_PzJeps_iter_succ_le {α ε C₀ Cj B τ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {F : Fn → Fn} {h₀ : Fn} {n : ℕ}
    (hρ : IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1) (hε : 0 < ε) (hτ : 0 ≤ τ) (hB : 0 ≤ B)
    (hCj : 0 ≤ Cj)
    (hgate : ∀ f : Fn, Work.FTS.EllipticEst.SmoothOpen f → EpsMem α f →
      Work.Spaces.HkSq α 4 (Pz (Jeps ρ ε f)) ≤ Cj * EpsSq α f)
    (hsm0 : Work.FTS.EllipticEst.SmoothOpen h₀)
    (hsmU : Work.FTS.EllipticEst.SmoothOpen (slice (iter F h₀ (n + 1)) τ))
    (hm0 : Work.Spaces.HkMem α 4 h₀)
    (hmU : Work.Spaces.HkMem α 4 (slice (iter F h₀ (n + 1)) τ))
    (hGmeas : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => F (slice (iter F h₀ n) p.1) p.2.1 p.2.2 * epsW α p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)).prod DomM))
    (hGbd : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)),
      epsL2 α (F (slice (iter F h₀ n) s)) ≤ ENNReal.ofReal B)
    (hxn0 : Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε h₀)) ≤ C₀ * α ^ 2) :
    Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε (slice (iter F h₀ (n + 1)) τ)))
      ≤ C₀ * α ^ 2 + Real.sqrt (Cj * (τ * (τ * B))) := by
  -- the increment
  have hslice : slice (iter F h₀ (n + 1)) τ
      = fun z θ => h₀ z θ + ∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ n) s) z θ := by
    funext z θ
    simp only [Work.FTS.Galerkin.slice_apply, iter_succ]
  have hdiff : (fun z θ => slice (iter F h₀ (n + 1)) τ z θ - h₀ z θ)
      = fun z θ => ∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ n) s) z θ := by
    funext z θ
    rw [hslice]
    ring
  have hincr := Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.EpsMem_and_EpsSq_intervalIntegral_le
    (α := α) (τ := τ) (B := B) hτ hB hGmeas hGbd
  have hepsmem : EpsMem α (fun z θ => slice (iter F h₀ (n + 1)) τ z θ - h₀ z θ) :=
    EpsMem_congr_pt (fun z θ => (congrFun (congrFun hdiff z) θ).symm) hincr.1
  have hepssq : EpsSq α (fun z θ => slice (iter F h₀ (n + 1)) τ z θ - h₀ z θ)
      ≤ τ * (τ * B) := by
    rw [show (fun z θ => slice (iter F h₀ (n + 1)) τ z θ - h₀ z θ)
        = (fun z θ => ∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ n) s) z θ) from hdiff]
    exact hincr.2
  have hb := hgate (fun z θ => slice (iter F h₀ (n + 1)) τ z θ - h₀ z θ)
    (Work.FTS.EllipticEst.smoothOpen_sub hsmU hsm0) hepsmem
  have hb' : Work.Spaces.HkSq α 4 (Pz (Jeps ρ ε (fun z θ =>
      slice (iter F h₀ (n + 1)) τ z θ - h₀ z θ))) ≤ Cj * (τ * (τ * B)) :=
    hb.trans (mul_le_mul_of_nonneg_left hepssq hCj)
  have htr := Xn_PzJeps_sub_le hρ hα hε hsmU hsm0 hmU hm0 hb'
  refine htr.trans (add_le_add hxn0 ?_)
  exact Real.sqrt_le_sqrt le_rfl

end Work.FTS.EpsEngine
