/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EpsE4Thr/AprioriFourthLevel.lean` — the level-four a-priori from the barrier level, with the
energy identity only at the barrier level

This module assembles the level-four small-ball a-priori bound of the `ε`-scheme in the *sharp*
form forced by the barrier (`AprioriHalves.AprioriPFourth`):

1. the barrier (`BarrierLevel.barrier_within_level_Ico`) is run on the pairing
   `E τ = IP α x_τ x_τ` at the level `Y ≤ clo (C₀ α²)²`; it consumes the energy *derivative* and
   its strict negativity **only at the times `τ` with `E τ = Y`** — the circularity of the old
   interface (the derivative had to be available everywhere, hence the ball everywhere) disappears;
2. `BallAtLevel.ballAt_of_energy_bound` converts the barrier conclusion `E τ ≤ Y` into the ball
   `Xn α x_τ ≤ C₀ α²` through the lower comparability `UnifIPO.lo`;
3. the datum condition is the *strict* one `Xn α x_0 < √(clo/Cup)·(C₀ α²)`
   (`BallAtLevel.IP_lt_level_of_norm_lt`), which is what makes the barrier start.

The last form `apriori_fourth_of_barrier_level_norm` is the one a producer should aim at; the
factor `√(clo/Cup) ≤ 1` is essential and cannot be removed from the `τ = 0` hypothesis — see
`NOTES_EpsE4Thr_session12.md` §3 for the discussion and for the way in which the current
`AprioriPFourth` (which asks for the datum merely *in* the ball) is out of reach of this route.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.EpsE4Thr.BarrierLevel
import Submission.Work.FTS.StrongEps.EpsE4Thr.BallAtLevel
import Submission.Work.FTS_MuLamOK.Main

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The level-four a-priori from the barrier level.**

Given a curve `x : ℝ → Fn` with `CoerAdmO α (x τ)` for `τ ∈ Ico 0 T`, whose pairing
`E τ = IP α (x τ) (x τ)` is continuous, starts below the level `Y ≤ clo (C₀ α²)²`, and has a
strictly negative within-derivative at every time at which `E τ = Y`, the curve stays in the
`C₀ α²`-ball.

The derivative hypothesis is needed *only at the level* — this is the improvement over
`apriori_fourth_of_barrier[_open]`, and it is what makes the energy identity usable at all
(its producer needs the ball, which is only available at the level, via `E τ = Y` and
`BallAtLevel.ballAt_of_IP_eq`). -/
theorem apriori_fourth_of_barrier_level {IP : ℝ → Fn → Fn → ℝ} {α₂ cc clo Cup Ccs : ℝ}
    (hIP : UnifIPO IP α₂ cc clo Cup Ccs)
    {α C₀ Y T : ℝ} {x : ℝ → Fn} {E4' : ℝ → ℝ}
    (hα : α ∈ Set.Ioc 0 α₂) (hC₀ : 0 ≤ C₀) (hT : 0 < T)
    (hYle : Y ≤ clo * (C₀ * α ^ 2) ^ 2)
    (hcoer : ∀ τ ∈ Set.Ico 0 T, CoerAdmO α (x τ))
    (hcont : ContinuousOn (fun τ => IP α (x τ) (x τ)) (Set.Ico 0 T))
    (h0 : IP α (x 0) (x 0) < Y)
    (hderiv : ∀ τ ∈ Set.Ico 0 T, IP α (x τ) (x τ) = Y →
      HasDerivWithinAt (fun s => IP α (x s) (x s)) (E4' τ) (Set.Icc 0 T) τ)
    (hneg : ∀ τ ∈ Set.Ico 0 T, IP α (x τ) (x τ) = Y → E4' τ < 0) :
    ∀ τ ∈ Set.Ico 0 T, Work.FTS.Nonlin.Xn α (x τ) ≤ C₀ * α ^ 2 :=
  ballAt_of_energy_bound hIP hα hC₀ hYle hcoer
    (barrier_within_level_Ico hT hcont hderiv h0 hneg)

/-- **The same, with the endpoint included and the one-sided limit hypothesis.** -/
theorem apriori_fourth_of_barrier_level_endpoint {IP : ℝ → Fn → Fn → ℝ}
    {α₂ cc clo Cup Ccs : ℝ} (hIP : UnifIPO IP α₂ cc clo Cup Ccs)
    {α C₀ Y T : ℝ} {x : ℝ → Fn} {E4' : ℝ → ℝ}
    (hα : α ∈ Set.Ioc 0 α₂) (hC₀ : 0 ≤ C₀) (hT : 0 < T)
    (hYle : Y ≤ clo * (C₀ * α ^ 2) ^ 2)
    (hcoer : ∀ τ ∈ Set.Icc 0 T, CoerAdmO α (x τ))
    (hcont : ContinuousOn (fun τ => IP α (x τ) (x τ)) (Set.Ico 0 T))
    (h0 : IP α (x 0) (x 0) < Y)
    (hderiv : ∀ τ ∈ Set.Ico 0 T, IP α (x τ) (x τ) = Y →
      HasDerivWithinAt (fun s => IP α (x s) (x s)) (E4' τ) (Set.Icc 0 T) τ)
    (hneg : ∀ τ ∈ Set.Ico 0 T, IP α (x τ) (x τ) = Y → E4' τ < 0)
    (hcontT : ContinuousWithinAt (fun τ => IP α (x τ) (x τ)) (Set.Icc 0 T) T) :
    ∀ τ ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α (x τ) ≤ C₀ * α ^ 2 := by
  have hIco : ∀ τ ∈ Set.Ico 0 T, Work.FTS.Nonlin.Xn α (x τ) ≤ C₀ * α ^ 2 :=
    apriori_fourth_of_barrier_level hIP hα hC₀ hT hYle
      (fun τ hτ => hcoer τ ⟨hτ.1, hτ.2.le⟩) hcont h0 hderiv hneg
  intro τ hτ
  rcases lt_or_eq_of_le hτ.2 with h | h
  · exact hIco τ ⟨hτ.1, h⟩
  · have hτT : τ = T := h
    -- the ball at the endpoint follows from the level bound at `T`
    have hall := barrier_within_level_endpoint hT hcont hderiv h0 hneg hcontT
    have hlim : IP α (x T) (x T) ≤ Y := hall T ⟨hT.le, le_rfl⟩
    rw [hτT]
    exact ballAt_of_IP_eq hIP hα (hcoer T ⟨hτT ▸ hτ.1, le_rfl⟩) hC₀ hlim hYle

/-- **The consumer form: the strict datum condition.**

If the datum's `ℋ⁴`-size is strictly below `√(clo/Cup)·(C₀ α²)` (and `Y := clo (C₀ α²)²`), the
barrier hypothesis `IP α (x 0) (x 0) < Y` is automatic, and the conclusion is the small ball.

This is the precise form of the level-four a-priori's datum hypothesis: the extra factor
`√(clo/Cup) ≤ 1` is *not* a technicality — the barrier cannot be started from the datum's mere
membership in the `C₀ α²`-ball whenever `clo < Cup`. -/
theorem apriori_fourth_of_barrier_level_norm {IP : ℝ → Fn → Fn → ℝ} {α₂ cc clo Cup Ccs : ℝ}
    (hIP : UnifIPO IP α₂ cc clo Cup Ccs)
    {α C₀ T : ℝ} {x : ℝ → Fn} {E4' : ℝ → ℝ}
    (hα : α ∈ Set.Ioc 0 α₂) (hC₀ : 0 ≤ C₀) (hT : 0 < T)
    (hcoer : ∀ τ ∈ Set.Ico 0 T, CoerAdmO α (x τ))
    (hcont : ContinuousOn (fun τ => IP α (x τ) (x τ)) (Set.Ico 0 T))
    (hdatum : Work.FTS.Nonlin.Xn α (x 0) < Real.sqrt (clo / Cup) * (C₀ * α ^ 2))
    (hderiv : ∀ τ ∈ Set.Ico 0 T, IP α (x τ) (x τ) = clo * (C₀ * α ^ 2) ^ 2 →
      HasDerivWithinAt (fun s => IP α (x s) (x s)) (E4' τ) (Set.Icc 0 T) τ)
    (hneg : ∀ τ ∈ Set.Ico 0 T, IP α (x τ) (x τ) = clo * (C₀ * α ^ 2) ^ 2 → E4' τ < 0) :
    ∀ τ ∈ Set.Ico 0 T, Work.FTS.Nonlin.Xn α (x τ) ≤ C₀ * α ^ 2 :=
  apriori_fourth_of_barrier_level hIP hα hC₀ hT le_rfl hcoer hcont
    (IP_lt_level_of_norm_lt hIP hα (hcoer 0 ⟨le_rfl, hT⟩) hdatum) hderiv hneg

/-- **The level-four a-priori in the form the *endpoint* energy identity produces.**

This is the trap barrier (`BarrierLevel.barrier_within_level_left`) composed with the conversions of
`BallAtLevel`, in the form the level-four chapter can actually run:

* the level-point data `hlev` is required only for the times `τ` at which the level is met *and* the
  ball is known on `[0,τ]` — which is exactly the input hypothesis of the endpoint energy identity
  (`EnergyDerivLeft.lean`) and of the `hneg` split;
* the ball on `[0,τ]` is recovered inside from the level bound on `[0,τ)` (via `UnifIPO.lo`), so a
  producer only has to supply the level bound.

The conclusion is the small ball with the *same* constant `C₀` as the level. -/
theorem ball_of_barrier_left {IP : ℝ → Fn → Fn → ℝ} {α₂ cc clo Cup Ccs : ℝ}
    (hIP : UnifIPO IP α₂ cc clo Cup Ccs)
    {α C₀ T : ℝ} {x : ℝ → Fn} {E4' : ℝ → ℝ}
    (hα : α ∈ Set.Ioc 0 α₂) (hC₀ : 0 ≤ C₀) (hT : 0 < T)
    (hcoer : ∀ τ ∈ Set.Icc 0 T, CoerAdmO α (x τ))
    (hcont : ContinuousOn (fun τ => IP α (x τ) (x τ)) (Set.Ico 0 T))
    (h0 : IP α (x 0) (x 0) < clo * (C₀ * α ^ 2) ^ 2)
    (hlev : ∀ τ ∈ Set.Ioo 0 T,
      (∀ t ∈ Set.Icc 0 τ, Work.FTS.Nonlin.Xn α (x t) ≤ C₀ * α ^ 2) →
      IP α (x τ) (x τ) = clo * (C₀ * α ^ 2) ^ 2 →
      HasDerivWithinAt (fun s => IP α (x s) (x s)) (E4' τ) (Set.Icc 0 τ) τ ∧ E4' τ < 0) :
    ∀ τ ∈ Set.Ico 0 T, Work.FTS.Nonlin.Xn α (x τ) ≤ C₀ * α ^ 2 := by
  have hbar : ∀ τ ∈ Set.Ico 0 T, IP α (x τ) (x τ) ≤ clo * (C₀ * α ^ 2) ^ 2 := by
    refine barrier_within_level_left (E := fun τ => IP α (x τ) (x τ)) (E' := E4') hT
      hcont h0 ?_
    intro τ hτ hlt hτY
    -- the level bound on `[0,τ)` gives the ball on `[0,τ]`
    have hball : ∀ t ∈ Set.Icc 0 τ, Work.FTS.Nonlin.Xn α (x t) ≤ C₀ * α ^ 2 := by
      intro t ht
      refine ballAt_of_IP_eq hIP hα (hcoer t ⟨ht.1, ht.2.trans hτ.2.le⟩) hC₀ ?_ le_rfl
      rcases lt_or_eq_of_le ht.2 with h | h
      · exact hlt t ⟨ht.1, h⟩
      · rw [h]; exact le_of_eq hτY
    exact hlev τ hτ hball hτY
  exact fun τ hτ =>
    ballAt_of_IP_eq hIP hα (hcoer τ ⟨hτ.1, hτ.2.le⟩) hC₀ (hbar τ hτ) le_rfl

/-- **The level-four a-priori from the datum's ball, with the (sharp) constant inflation.**

This is the consumer-facing form of `ball_of_barrier_left`: the *datum* is only assumed to lie in
the `K₀ α²`-ball (which is what the target's hypotheses give, with `K₀ = 1`), and the conclusion is
the ball with the *larger* constant `K'`.  The two are related by

  `Cup · K₀² < clo · K'²`   (i.e. `K' > K₀·√(Cup/clo)`),

which is exactly the condition that the datum's *energy* `IP α x₀ x₀ ≤ Cup·(K₀α²)²` be strictly
below the level `clo·(K'α²)²` at which the barrier is started.

The factor `√(Cup/clo) ≥ 1` (equal to `1` iff `clo = Cup`) is *not* removable from this argument:
the barrier level has to be simultaneously `> E 0 ≳ Cup(K₀α²)²` and `≤ clo(K'α²)²`.  For the
level-four pairing of the `ε`-scheme the two constants come from `lo_four_open`/`up_four_open`, and
`Cup/clo` is astronomically large; this is the quantitative form of the session-1 finding that the
constant `C₀ = 1` of `EpsE4Thr`/`EpsUniformMem` is saturated (see `NOTES_EpsE4Thr_session12.md`
§4). -/
theorem ball_of_barrier_datum_ball {IP : ℝ → Fn → Fn → ℝ} {α₂ cc clo Cup Ccs : ℝ}
    (hIP : UnifIPO IP α₂ cc clo Cup Ccs)
    {α K₀ K' T : ℝ} {x : ℝ → Fn} {E4' : ℝ → ℝ}
    (hα : α ∈ Set.Ioc 0 α₂) (hK' : 0 < K') (hT : 0 < T)
    (hratio : Cup * K₀ ^ 2 < clo * K' ^ 2)
    (hcoer : ∀ τ ∈ Set.Icc 0 T, CoerAdmO α (x τ))
    (hcont : ContinuousOn (fun τ => IP α (x τ) (x τ)) (Set.Ico 0 T))
    (hdatum : Work.FTS.Nonlin.Xn α (x 0) ≤ K₀ * α ^ 2)
    (hlev : ∀ τ ∈ Set.Ioo 0 T,
      (∀ t ∈ Set.Icc 0 τ, Work.FTS.Nonlin.Xn α (x t) ≤ K' * α ^ 2) →
      IP α (x τ) (x τ) = clo * (K' * α ^ 2) ^ 2 →
      HasDerivWithinAt (fun s => IP α (x s) (x s)) (E4' τ) (Set.Icc 0 τ) τ ∧ E4' τ < 0) :
    ∀ τ ∈ Set.Ico 0 T, Work.FTS.Nonlin.Xn α (x τ) ≤ K' * α ^ 2 := by
  have hCup : 0 < Cup := hIP.pos.2.2.2.1
  have hclo : 0 < clo := hIP.pos.2.2.1
  have hα0 : 0 ≤ α := hα.1.le
  have hK0 : 0 ≤ K₀ := by
    by_contra h
    have h2 : K₀ * α ^ 2 < 0 := mul_neg_of_neg_of_pos (not_le.mp h) (pow_pos hα.1 2)
    linarith [Work.Spaces.HkNorm_nonneg α 4 (x 0)]
  have h0 : IP α (x 0) (x 0) < clo * (K' * α ^ 2) ^ 2 := by
    have hup := hIP.up α hα (x 0) (hcoer 0 ⟨le_rfl, hT.le⟩)
    have hsq : Work.Spaces.HkSq α 4 (x 0) = (Work.FTS.Nonlin.Xn α (x 0)) ^ 2 := by
      change Work.Spaces.HkSq α 4 (x 0) = (Work.Spaces.HkNorm α 4 (x 0)) ^ 2
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 (x 0))]
    have hsqle : Work.Spaces.HkSq α 4 (x 0) ≤ (K₀ * α ^ 2) ^ 2 := by
      rw [hsq]
      exact pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 (x 0)) hdatum 2
    have hK'nn : 0 ≤ K' * α ^ 2 := mul_nonneg hK'.le (pow_nonneg hα0 2)
    have hK0nn : 0 ≤ K₀ * α ^ 2 := mul_nonneg hK0 (pow_nonneg hα0 2)
    have hsquares : (K₀ * α ^ 2) ^ 2 = K₀ ^ 2 * α ^ 4 := by ring
    have hsquares' : (K' * α ^ 2) ^ 2 = K' ^ 2 * α ^ 4 := by ring
    have ha4 : 0 < α ^ 4 := pow_pos hα.1 4
    calc IP α (x 0) (x 0) ≤ Cup * Work.Spaces.HkSq α 4 (x 0) := hup
      _ ≤ Cup * (K₀ * α ^ 2) ^ 2 := mul_le_mul_of_nonneg_left hsqle hCup.le
      _ = Cup * K₀ ^ 2 * α ^ 4 := by rw [hsquares]; ring
      _ < clo * K' ^ 2 * α ^ 4 := mul_lt_mul_of_pos_right hratio ha4
      _ = clo * (K' * α ^ 2) ^ 2 := by rw [hsquares']; ring
  exact ball_of_barrier_left hIP hα hK'.le hT hcoer hcont h0 hlev

/-! ## The radius upgrade of the modulation clause

The target's hypothesis is `hml : MuLamOK α C₀ Φs E`, i.e. the μ/λ-clause at the **single** radius
`C₀ α²`.  Every producer on the level-four route needs it at the radius of the *level* at which the
barrier is run — which is strictly larger than `C₀` whenever the datum must be strictly inside the
level (see `ball_of_barrier_datum_ball`).  This is not an interface item: the chapter `FTS_MuLamOK`
proves the clause at *every* class-`C` ball, for `α` below a threshold depending only on the
radius constant. -/

/-- **The radius upgrade of `MuLamOK`.**

`Work.FTS_MuLamOK.MuLamOK_proved_eventually` gives the μ/λ-clause at the radius `C₀'` for `α` below
a threshold depending on `C₀'`, `Ce`, `Cs`, from the packages `EllPkgGo` (the `EllPkgK` half of
`hEll` is not used) and `StarPkgo2`; monotonicity of the clause in its size constant
(`MuLamOK_mono_C₀`) then downgrades `C₀' = max K 1` to the caller's `K`.  So along the `ε`-scheme
the modulation bounds are available on the class-`C` ball of *any* radius `K α²`. -/
theorem MuLamOK_of_hEll_hstar {Ce Cs K : ℝ} (hK : 0 ≤ K) :
    ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α ∈ Set.Ioc 0 α₀, ∀ {Φs : Fn} {E : Fn → Fn},
      (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
        Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
      Work.FTS.StrongEps.MuLamOK α K Φs E := by
  obtain ⟨α₂, hα₂, hmain⟩ := Work.FTS_MuLamOK.MuLamOK_proved_eventually (C₀ := max K 1)
    (Ce := Ce) (Cs := Cs) (lt_max_of_lt_right zero_lt_one)
  exact ⟨α₂, hα₂, fun α hα Φs E hEll hstar =>
    Work.FTS_MuLamOK.MuLamOK_mono_C₀
      (hmain α hα hstar fun f hf => (hEll f hf).1) (le_max_left K 1)⟩

end Work.FTS.StrongEps.EpsE4Thr
