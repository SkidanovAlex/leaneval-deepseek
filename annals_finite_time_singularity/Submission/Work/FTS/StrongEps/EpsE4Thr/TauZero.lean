/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/TauZero.lean` — the fake-time-`0` obligation of `EpsE4Thr`

## The finding

`EpsUniformMem α ρ Φs E g₀ C₀ K`'s clause at the fake time `τ = 0` reads
(`EpsE4Work/epsUniformMem_Jeps_bound.lean`, proved)

  `Xn α (slice (JfamP ρ ε g) 0) = Xn α (J_ε g₀) ≤ C₀ * α²`   for every `ε ∈ (0, ε₁]`,

where the middle identity uses the `l12`-field of `hd : ∀ ε > 0, EpsDatum α ρ ε g₀` to see that
`P₀` acts trivially.  The *datum* hypotheses of `EpsE4Thr` give only `Xn α g₀ ≤ α²` (`h4`), so the
`C₀ = 1` case of the repair `hC₀ : 1 ≤ C₀` requires

  `Xn α (J_ε g₀) ≤ Xn α g₀`   for every small `ε`,

i.e. **monotonicity of the weighted `ℋ⁴`-norm under the log-coordinate mollifier** — which is
*not* in the workspace (`HkSq_Jeps_le` gives only the upper bound `e^{Cε} HkSq`, and the `+ε`
factor is intrinsic: the weight ratio `w(z) / w(zShift z p)` genuinely exceeds `1` for inward
shifts `p > 0`).  The present module records the two halves of that finding that *are* provable
today:

* `Jeps_smallBall_one_lt` — the `τ = 0` obligation holds, for `ε` small, as soon as **`1 < C₀`**:
  the mollifier-approximation estimate `‖J_ε g₀ − g₀‖_{ℋ⁴} ≤ C ε ‖g₀‖_{ℋ⁵}`
  (`EpsApprox.HkNorm_Jeps_sub_le`) and the **sharp** triangle inequality `HkNorm_triangle`
  (proved next door, from `HkIntegrand_sqrt_add_le` + `HkIntegrand_sqrt_integrable`) give
  `Xn α (J_ε g₀) ≤ Xn α g₀ + C ε ‖g₀‖_{ℋ⁵} ≤ α² + C ε ‖g₀‖_{ℋ⁵}`, and the linear error is
  absorbed by the gap `C₀ − 1 > 0` for `ε ≤ (C₀ − 1) α² / (C (‖g₀‖₅ + 1))`.  Hence the repair
  `hC₀ : 1 ≤ C₀` *is* sufficient on the open range `C₀ > 1` — the honest threshold, since the
  `τ = 0` clause is *equivalent* (as `ε → 0`) to `Xn α g₀ ≤ C₀ α²`
  (`EpsE4Work.Xn_le_sqrt_two_mul_of_Jeps_bound`'s argument) and `h4` gives exactly `α²`;
* `certificate_datum_one_needs_monotone` — the `C₀ = 1` case is *saturated* (see below).

So: the C₀ = 1 case of `EpsE4Thr` needs *either* the monotonicity of `J_ε` on `ℋ⁴` (false in
general — a plateau profile of log-width large compared with the kernel's second moment *increases*
the norm: the second-order term of `HkSq (J_ε f) − HkSq f` is `(1/2)M₂ G''(0)` with
`G''(0) = −∫F'²W + (1/2)∫F²W''` and `W'' ≥ (2/3)W`) *or* the **strict** `h4`-form
`Xn α g₀ < C₀ α²` (equivalently `C₀` strictly larger than `1`).  This is the same finding, in sharper form, as
`EpsE4Work/NOTES_EpsE4_FALSE.md` §3.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsApprox.HkNorm_Jeps_sub_le
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.StrongEps.EpsE4Thr.HkNorm_triangle
import Submission.Work.FTS.StrongEps.EpsE4Work.epsUniformMem_Jeps_bound
import Submission.Work.FTS.StrongEps.EpsE4Work.Certificate
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.StrongPersist.Basic
import Submission.Work.FTS.EllipticEst.HkMem_add_smoothOpen
import Submission.Work.FTS.EllipticEst.HkSq_congr_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Three small closure facts for the `ℋ^k`-machinery (as in the certificate module) -/

/-- `SmoothOpen` of a pointwise negation. -/
private theorem smoothOpen_neg {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => -f z θ) := by
  have hfun : Function.uncurry (fun z θ => -f z θ) = -(Function.uncurry f) := by
    funext p; rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, hfun]
  exact hf.neg

/-- `HkMem` of a pointwise negation: the `ℋ^k`-integrand of `-f` *equals* that of `f`. -/
private theorem hkMem_neg {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α k f) : Work.Spaces.HkMem α k (fun z θ => -f z θ) := by
  have hI : ∀ z θ, Work.Spaces.HkIntegrand α k (fun z θ => -f z θ) z θ
      = Work.Spaces.HkIntegrand α k f z θ :=
    fun z θ => congrFun (congrFun (Work.FTS.EllipticEst.HkIntegrand_neg α k f) z) θ
  constructor
  · intro z hz
    exact (hf.1 z hz).congr_fun (fun θ _ => (hI z θ).symm) measurableSet_Icc
  · have h : (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => -f z θ) z θ)
        = fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
      funext z
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => hI z θ)
    rw [h]
    exact hf.2

/-- `ℋ^k` is closed under subtraction for profiles smooth on the open quadrant. -/
private theorem hkMem_sub {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => f z θ - g z θ) := by
  have hfun : (fun z θ => f z θ - g z θ) = (fun z θ => f z θ + -g z θ) := by
    funext z θ; ring
  rw [hfun]
  exact Work.FTS.EllipticEst.HkMem_add_open hf (smoothOpen_neg hg) hmf (hkMem_neg hmg)

/-- `HkNorm` only sees the pointwise values of the profile. -/
private theorem hkNorm_congr_pt {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ, f z θ = g z θ) : Work.Spaces.HkNorm α k f = Work.Spaces.HkNorm α k g := by
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm,
    Work.FTS.EllipticEst.HkSq_congr_open α k (fun z θ _ _ _ => h z θ)]

/-! ## The `τ = 0` obligation of `EpsE4Thr` -/

/-- **The fake-time-`0` obligation of `EpsE4Thr` for `1 < C₀`.**

For a datum of the `hd`-class with `Xn α g₀ ≤ α²`, the projected mollified profile `J_ε g₀` lies in
the `C₀ α²`-ball for all sufficiently small `ε`.  (The statement is the *converse* of
`EpsE4Work/epsUniformMem_Jeps_bound.lean`, which extracts the same clause *from* the conclusion of
`EpsE4Thr`.)

*Proof.*  `J_ε g₀ = g₀ + (J_ε g₀ − g₀)`; the sharp triangle inequality `HkNorm_triangle` gives
`Xn α (J_ε g₀) ≤ Xn α g₀ + Xn α (J_ε g₀ − g₀)`, and the approximation estimate bounds the second
summand by `C ε Xn₅ α g₀`; the linear error is absorbed by the gap `C₀ − 1 > 0` once
`ε ≤ (C₀ − 1) α² / (C (Xn₅ α g₀ + 1))`. -/
theorem Jeps_smallBall_one_lt {α C₀ : ℝ} {ρ : ℝ × ℝ → ℝ} {g₀ : Fn}
    (hρ : IsSmoothKernel ρ) (hα : 0 < α) (hα1 : α ≤ 1) (hC₀ : 1 < C₀)
    (hd : ∀ ε : ℝ, 0 < ε → EpsDatum α ρ ε g₀)
    (h4 : Work.FTS.Nonlin.Xn α g₀ ≤ α ^ 2) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε ∈ Set.Ioc 0 ε₁,
      Work.FTS.Nonlin.Xn α (Jeps ρ ε g₀) ≤ C₀ * α ^ 2 := by
  -- the datum-side regularity of `hd`
  have hsm : Work.FTS.EllipticEst.SmoothOpen g₀ := (hd 1 one_pos).1
  have h6 : Work.Spaces.HkMem α 6 g₀ := (hd 1 one_pos).2.1
  have h5 : Work.Spaces.HkMem α 5 g₀ :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hsm h6
  have hm4 : Work.Spaces.HkMem α 4 g₀ := Work.FTS.OpenPkg.HkMem_four_of_five hsm h5
  -- the mollifier-approximation estimate
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongEps.EpsApprox.HkNorm_Jeps_sub_le ρ hρ.moll
  have hαIoc : α ∈ Set.Ioc 0 1 := ⟨hα, hα1⟩
  have hα2 : 0 < α ^ 2 := pow_pos hα 2
  -- the gap produced by `1 < C₀`
  have hgap : 0 < C₀ - 1 := sub_pos.mpr hC₀
  have hden : 0 < C * (Work.Spaces.HkNorm α 5 g₀ + 1) :=
    mul_pos hCpos (by linarith [Work.Spaces.HkNorm_nonneg α 5 g₀])
  refine ⟨min 1 ((C₀ - 1) * α ^ 2 / (C * (Work.Spaces.HkNorm α 5 g₀ + 1))),
    lt_min one_pos (div_pos (mul_pos hgap hα2) hden), ?_⟩
  intro ε hε
  have hε1 : ε ≤ 1 := le_trans hε.2 (min_le_left _ _)
  have hεb : ε ≤ (C₀ - 1) * α ^ 2 / (C * (Work.Spaces.HkNorm α 5 g₀ + 1)) :=
    le_trans hε.2 (min_le_right _ _)
  have hεIoc : ε ∈ Set.Ioc 0 1 := ⟨hε.1, hε1⟩
  -- the two summands
  set J : ℝ → ℝ → ℝ := Jeps ρ ε g₀ with hJdef
  have hJsm : Work.FTS.EllipticEst.SmoothOpen J := (hd ε hε.1).2.2.reg
  have hJ7 : Work.Spaces.HkMem α 7 J := (hd ε hε.1).2.2.mem
  have hJmem : Work.Spaces.HkMem α 4 J :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hJsm hJ7
  have hDsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => J z θ - g₀ z θ) :=
    Work.FTS.EllipticEst.smoothOpen_sub hJsm hsm
  have hDmem : Work.Spaces.HkMem α 4 (fun z θ => J z θ - g₀ z θ) :=
    hkMem_sub hJsm hsm hJmem hm4
  -- the *sharp* triangle inequality for `J = g₀ + (J - g₀)`
  have htri : Work.Spaces.HkNorm α 4 (fun z θ => g₀ z θ + (J z θ - g₀ z θ))
      ≤ Work.Spaces.HkNorm α 4 g₀
          + Work.Spaces.HkNorm α 4 (fun z θ => J z θ - g₀ z θ) :=
    HkNorm_triangle α 4
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall g₀).mp hsm)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hDsm) hm4 hDmem
  have hcongr : Work.Spaces.HkNorm α 4 J
      = Work.Spaces.HkNorm α 4 (fun z θ => g₀ z θ + (J z θ - g₀ z θ)) :=
    hkNorm_congr_pt (fun z θ => by ring)
  -- the approximation error
  have happ : Work.Spaces.HkNorm α 4 (fun z θ => J z θ - g₀ z θ)
      ≤ C * ε * Work.Spaces.HkNorm α 5 g₀ :=
    hC α hαIoc 4 ε hεIoc g₀ ((Work.FTS.EllipticEst.smoothOpen_iff_forall g₀).mp hsm) h5 hJmem
  -- the datum's bound
  have hg0 : Work.Spaces.HkNorm α 4 g₀ ≤ α ^ 2 := by
    simpa only [Work.FTS.Nonlin.Xn] using h4
  -- assembling
  have hstep : Work.Spaces.HkNorm α 4 J
      ≤ α ^ 2 + C * ε * (Work.Spaces.HkNorm α 5 g₀ + 1) := by
    rw [hcongr]
    refine htri.trans ?_
    have hN5' : C * ε * Work.Spaces.HkNorm α 5 g₀ ≤ C * ε * (Work.Spaces.HkNorm α 5 g₀ + 1) := by
      have : Work.Spaces.HkNorm α 5 g₀ ≤ Work.Spaces.HkNorm α 5 g₀ + 1 := by linarith
      exact mul_le_mul_of_nonneg_left this (mul_nonneg hCpos.le hε.1.le)
    linarith [add_le_add hg0 (happ.trans hN5')]
  -- the error term is small: `C ε (‖g₀‖₅ + 1) ≤ (C₀ - 1) α²`
  have hεC : C * ε * (Work.Spaces.HkNorm α 5 g₀ + 1) ≤ (C₀ - 1) * α ^ 2 := by
    have h2 : ε * (C * (Work.Spaces.HkNorm α 5 g₀ + 1))
        ≤ ((C₀ - 1) * α ^ 2 / (C * (Work.Spaces.HkNorm α 5 g₀ + 1)))
          * (C * (Work.Spaces.HkNorm α 5 g₀ + 1)) :=
      mul_le_mul_of_nonneg_right hεb hden.le
    rw [div_mul_cancel₀ _ hden.ne'] at h2
    have h3 : C * ε * (Work.Spaces.HkNorm α 5 g₀ + 1)
        = ε * (C * (Work.Spaces.HkNorm α 5 g₀ + 1)) := by
      ring
    rw [h3]; exact h2
  calc Work.FTS.Nonlin.Xn α J = Work.Spaces.HkNorm α 4 J := rfl
    _ ≤ α ^ 2 + C * ε * (Work.Spaces.HkNorm α 5 g₀ + 1) := hstep
    _ ≤ α ^ 2 + (C₀ - 1) * α ^ 2 := add_le_add le_rfl hεC
    _ = C₀ * α ^ 2 := by ring

/-- **The `C₀ = 1` case of `EpsE4Thr` forces the `ℋ⁴`-monotonicity of `J_ε` on the saturated
datum.**  This is the sharp form of the finding: for the certificate's datum — admissible for every
`ε > 0`, vanishing on the angular boundary, and of `ℋ⁴`-size *exactly* `α²`
(`EpsE4Work.exists_datum_Xn_eq`) — the conclusion of `EpsE4Thr` at `C₀ = 1` implies

  `∃ ε₁ > 0, ∀ ε ∈ (0, ε₁],  Xn α (J_ε g₀) ≤ Xn α g₀`,

i.e. the mollifier must *not* increase the weighted `ℋ⁴`-norm at that datum.  The hypotheses give
only `Xn α g₀ ≤ α²` (`h4`), and the conclusion's `τ = 0` clause reads `Xn α (J_ε g₀) ≤ C₀ α²`
(`EpsE4Work.epsUniformMem_Jeps_bound`), so at `C₀ = 1` that clause is *exactly* the monotonicity
statement on a saturated datum — the `α² ≤ C₀ α²` of the repair `hC₀ : 1 ≤ C₀` handles the
*limiting* inequality but not the `O(ε)` perturbation of the mollifier at each fixed `ε > 0`.

Consequence for the interface: `EpsE4Thr`'s `hC₀ : 1 ≤ C₀` is *tight*; the honest repairs are
`1 < C₀` (then the datum's `α²`-ball sits strictly inside the `C₀ α²`-ball and
`Jeps_smallBall_one_lt` discharges the `τ = 0`
clause) or the *strict* `h4`-form `Xn α g₀ < C₀ α²`. -/
theorem certificate_datum_one_needs_monotone {α : ℝ} {ρ : ℝ × ℝ → ℝ}
    (hρ : IsSmoothKernel ρ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ g₀ : Fn, (∀ ε : ℝ, 0 < ε → EpsDatum α ρ ε g₀) ∧
      Work.FTS.Nonlin.Xn α g₀ = α ^ 2 ∧
      (∀ z, 0 ≤ z → g₀ z 0 = 0 ∧ g₀ z (π / 2) = 0) ∧
      ∀ (Φs : Fn) (E : Fn → Fn) (K : ℝ),
        EpsUniformMem α ρ Φs E g₀ 1 K →
          ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε ∈ Set.Ioc 0 ε₁,
            Work.FTS.Nonlin.Xn α (Jeps ρ ε g₀) ≤ Work.FTS.Nonlin.Xn α g₀ := by
  obtain ⟨g₀, hd, hsize, hvan⟩ := Work.FTS.StrongEps.EpsE4Work.exists_datum_Xn_eq hρ hα hα1
  refine ⟨g₀, hd, hsize, hvan, ?_⟩
  intro Φs E K hU
  obtain ⟨ε₁, hε₁, hbd⟩ := Work.FTS.StrongEps.EpsE4Work.epsUniformMem_Jeps_bound hU hd
  refine ⟨ε₁, hε₁, fun ε hε => ?_⟩
  have := hbd ε hε
  rwa [one_mul, ← hsize] at this

end Work.FTS.StrongEps.EpsE4Thr
