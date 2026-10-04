import Mathlib
import Submission.Diff.Grad
import Submission.Diff.Evol
import Submission.Work.Diff.GE.Frame
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.FrameIndep
import Submission.Work.Diff.GE.rot_pair
import Submission.Work.Diff.GE.laplAt_rmNormSq_eq
import Submission.Work.Diff.GE.roughLap_rot
import Submission.Work.Diff.GE.derivWithin_Ico_zero
import Submission.Work.Diff.GE.flowContAtZero
import Submission.Work.Diff.GE.uhlenbeck_frame_coe
import Submission.Work.Diff.Evol.curv_evolution
import Submission.Work.Diff.Evol.curv_variation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

CONTEXT: this is one area of the Brendle–Schoen differentiable sphere theorem, driven by the lead. Read HANDOFF.md.
The contracts in Submission/Diff/Interfaces.lean and Submission/Diff/Alg.lean are frozen. Your statement's hypotheses are other
areas' contracts: USE them, do not re-prove them. Go wide: file all the independent sub-lemmas at once,
each with an exact statement, and write your assembly against their statements. If your statement looks
false or unprovable as stated, say so at once in `declare_false` with a precise reason. The lead will fix it.
ROUTE. Hamilton's evolution equations under Ricci flow (Hamilton 1982 §7, 13; Chow–Knopf ch. 6; Topping ch. 2).
Derive them from LCVariation with h = −2Ric.
Uhlenbeck trick: at fixed x, frames with ∂ₜeᵢ = Ric(eᵢ)^♯ stay G(t)-orthonormal, and in them the components
R_ijkl = g(R(eᵢ,eⱼ)eₗ, eₖ) satisfy ∂ₜR = ΔR + Q(R), with Q exactly as in Alg.lean.
Norms are frame-independent, so rmNormSq etc. may be computed in these frames.
SANITY (prove as a lemma first): Q (Iso n) = (2*(n−1)) • Iso n. ...


## Status of this file (state of the assembly)

The assembly is complete; every geometric input is an import.  The inputs, with their current
state on disk:

| input | module | state |
|---|---|---|
| chain rule `hasDerivAt_frobSq_comp` | this file | proved here |
| `rmNormSq_eq_frobSq_rmFrame`, `qPairAt_eq_qPair_rmFrame` | `Submission.Work.Diff.GE.FrameIndep` | proved (frame independence) |
| `rmFrame_eq_rot`, `onFrame_orthogonal_change` | `...GE.rmFrame_eq_rot`, `...GE.onFrame_orthogonal_change` | proved |
| `rot_frobsq`, `rot_qPair`, `rot_pair` | `...GE.rot_frobsq`, `...GE.rot_qPair`, `...GE.rot_pair` | proved |
| `roughLap_rot` | `...GE.roughLap_rot` | proved (frame change of the rough Laplacian) |
| `uhlenbeck_frame_coe` | `...GE.uhlenbeck_frame_coe` | proved (Uhlenbeck frame family, `E`-valued) |
| `derivWithin_Ico_zero` | `...GE.derivWithin_Ico_zero` | proved (endpoint: MVT plumbing) |
| `flowContAtZero` | `...GE.flowContAtZero` | proved (continuity at `0⁺`) |
| `lapl_rmNormSq` | `...GE.lapl_rmNormSq` | **the Kato identity** — statement on disk, prover in flight |
| `curv_evolution`, `curv_variation` | `Submission.Work.Diff.Evol.*` | proved (the shared contract `CurvEvolution`) |

So the only missing input of the whole reduction is the Kato/Weitzenböck identity
`Δ|Rm|² = 2⟨Rm,ΔRm⟩ + 2|∇Rm|²` (`Work.Diff.GE.lapl_rmNormSq`), whose statement is on disk; the
Kato-in-any-frame form used here is `laplAt_rmNormSq_eq_of_isONFrame` (proved from it plus frame
independence).  (An equivalent statement is also in flight as `...GE.laplAt_rmNormSq_eq`.)

## What is proved in THIS file (assembly of EV1, `EvolRmNormSq`)

Per the lead's re-organisation (`Submission/Diff/Evol.lean`), Hamilton's componentwise evolution
`∂ₜ R = ΔR + Q(R)` in an Uhlenbeck frame is the shared contract `CurvEvolution I M`, owned by
`Work.Diff.Evol.curv_evolution`.  This file contains only the *assembly* of EV1 from it:

* `hasDerivAt_frobSq_comp`: the chain rule `∂ₛ |R(s)|² = 2 ∑ Rₐ ∂ₛRₐ` for the curvature array;
* `laplAt_rmNormSq_eq_of_isONFrame`: the Kato/Weitzenböck identity in an *arbitrary* orthonormal
  frame (from the `onFrame` version `Work.Diff.GE.laplAt_rmNormSq_eq` by frame independence);
* `hasDerivAt_rmNormSq_of_CE_of_frame`: the interior derivation, given an Uhlenbeck frame family;
* `hasDerivWithinAt_rmNormSq_zero_of_CE`: the endpoint `t = 0` (mean-value/limit argument);
* `evol_rm_normsq_of_CE`: the full contract from `CurvEvolution I M`;
* `evol_rm_normsq`: the requested lemma, discharging `CurvEvolution I M` with the owner's
  `curv_evolution`/`curv_variation`.

The only *geometric* inputs are the shared contract `CurvEvolution` (componentwise evolution in an
Uhlenbeck frame) and the frame-independent statics: frame independence (`FrameIndep`), the Kato
identity and the Uhlenbeck frame existence (`Work.Diff.GE.uhlenbeck_frame_exists`).  The endpoint
`t = 0` needs continuity of `s ↦ rmNormSq` and of the right-hand side, which is
`Work.Diff.GE.continuous_flow_quantities` (a chart computation, REG-type content).
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [CompactSpace M]

/-! ## The chain rule for `frobSq` -/

/-- **The chain rule for the squared Frobenius norm.**  If the array of curvature components
`R s` has derivative `R'` at `t`, then the sum of squares has derivative `2 ∑ Rₐ R'ₐ`. -/
theorem hasDerivAt_frobSq_comp {n : ℕ} (R : ℝ → Curv4 n) (R' : Curv4 n) (t : ℝ)
    (h : HasDerivAt R R' t) :
    HasDerivAt (fun s ↦ frobSq (R s))
      (∑ i, ∑ j, ∑ k, ∑ l, 2 * R t i j k l * R' i j k l) t := by
  have hcoord : ∀ (i j k l : Fin n), HasDerivAt (fun s ↦ R s i j k l) (R' i j k l) t := by
    intro i j k l
    have h1 := hasDerivAt_pi.mp h
    have h2 := hasDerivAt_pi.mp (h1 i)
    have h3 := hasDerivAt_pi.mp (h2 j)
    exact hasDerivAt_pi.mp (h3 k) l
  have hsum : HasDerivAt (fun s ↦ ∑ i, ∑ j, ∑ k, ∑ l, (R s i j k l) ^ 2)
      (∑ i, ∑ j, ∑ k, ∑ l, 2 * R t i j k l * R' i j k l) t := by
    refine HasDerivAt.fun_sum (u := Finset.univ) fun i _ => ?_
    refine HasDerivAt.fun_sum (u := Finset.univ) fun j _ => ?_
    refine HasDerivAt.fun_sum (u := Finset.univ) fun k _ => ?_
    refine HasDerivAt.fun_sum (u := Finset.univ) fun l _ => ?_
    have h0 := HasDerivAt.pow (hcoord i j k l) 2
    convert h0 using 1
    ring
  simpa only [frobSq] using hsum

/-! ## The Kato identity in an arbitrary orthonormal frame -/

/-- **Kato/Weitzenböck identity for `|Rm|²`, in any orthonormal frame**:
`Δ|Rm|² = 2 ⟨Rm, ΔRm⟩ + 2 |∇Rm|²`, with the pairing and the rough Laplacian computed in the frame
`e`.  (The `onFrame` version is `Work.Diff.GE.laplAt_rmNormSq_eq`; this is the frame-independent
form used by the assembly.) -/
theorem laplAt_rmNormSq_eq_of_isONFrame (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e) :
    laplAt g (rmNormSq g) x
      = 2 * (∑ i, ∑ j, ∑ k, ∑ l, rmFrame g x e i j k l * lapRmFrame g x e i j k l)
        + 2 * dRmNormSq g x := by
  have hbase := Work.Diff.GE.laplAt_rmNormSq_eq hLC g x
  have he0 : IsONFrame g x (onFrame g x) := Work.Diff.GE.isONFrame_onFrame g x
  obtain ⟨A, hA, hAe⟩ := Work.Diff.GE.onFrame_orthogonal_change g x e (onFrame g x) he he0
  have hlap : Work.Diff.PP.roughLap g x (onFrame g x) = rot A (Work.Diff.PP.roughLap g x e) :=
    Work.Diff.GE.roughLap_rot hLC g x e (onFrame g x) A hAe hA
  have hfr : rmFrame g x (onFrame g x) = rot A (rmFrame g x e) :=
    Work.Diff.GE.rmFrame_eq_rot hLC g x e (onFrame g x) A hAe
  have h1 : (∑ i, ∑ j, ∑ k, ∑ l, rmFrame g x e i j k l * lapRmFrame g x e i j k l)
      = ∑ i, ∑ j, ∑ k, ∑ l, rmFrame g x e i j k l * Work.Diff.PP.roughLap g x e i j k l := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [Work.Diff.GE.lapRmFrame_eq_roughLap]
  have h2 : (∑ i, ∑ j, ∑ k, ∑ l, rmFrame g x e i j k l * Work.Diff.PP.roughLap g x e i j k l)
      = ∑ i, ∑ j, ∑ k, ∑ l,
          rmFrame g x (onFrame g x) i j k l * Work.Diff.PP.roughLap g x (onFrame g x) i j k l := by
    rw [hfr, hlap, Work.Diff.GE.rot_pair A hA]
  have hpair := h1.trans h2
  rw [hbase]
  simp only [rmC]
  rw [hpair]

/-! ## The interior derivation of `EvolRmNormSq`, given an Uhlenbeck frame -/

/-- A four-fold sum identity: `∑ 2 A (B + C) = 2 ∑ A B + 2 ∑ A C`. -/
theorem sum4_two_mul_add {n : ℕ} (A B C : Curv4 n) :
    (∑ i, ∑ j, ∑ k, ∑ l, 2 * A i j k l * (B i j k l + C i j k l))
      = 2 * (∑ i, ∑ j, ∑ k, ∑ l, A i j k l * B i j k l)
        + 2 * (∑ i, ∑ j, ∑ k, ∑ l, A i j k l * C i j k l) := by
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

/-- **Hamilton's identity for `|Rm|²` in the interior of the flow interval**, given a family of
frames at `x`, orthonormal for `G s`, differentiable at `t` with the Uhlenbeck derivative
`⟨∂ₛeᵢ, eⱼ⟩ = Ric(eᵢ,eⱼ)`.

Indeed `|Rm(G s)|² = ∑ (rmFrame (G s) x (e s))ₐ²` by frame independence, so by the chain rule its
derivative is `2 ∑ Rₐ ∂ₛRₐ`, and `∂ₛR = ΔR + Q(R)` (`CurvEvolution`, in the Uhlenbeck frame) turns
this into `2 ⟨Rm, ΔRm⟩ + 2 ⟪Rm, Q(Rm)⟫ = Δ|Rm|² − 2|∇Rm|² + 2 ⟪Rm, Q(Rm)⟫` by the Kato identity.

The frames are given as a family of *model-space* vectors (`E`), so that no normed structure on the
fibres of the tangent bundle is needed to state the differentiability of the frame; this is the same
convention as the frozen `LCVariation`. -/
theorem hasDerivAt_rmNormSq_of_CE_of_frame (hLC : LCSmooth I M) (hCE : CurvEvolution I M)
    (G : ℝ → SMet I M) (T : ℝ) (hflow : IsRicciFlow G T)
    (t : ℝ) (ht : t ∈ Set.Ioo 0 T) (x : M)
    (e : ℝ → Fin (Module.finrank ℝ E) → E)
    (hON : ∀ s ∈ Set.Ico 0 T, IsONFrame (G s) x (e s))
    (hder : ∀ i, HasDerivWithinAt (fun s : ℝ ↦ e s i)
        ((∑ j, ricAt (lcOf (G t)) x (e t i) (e t j) • e t j
          : TangentSpace I x) : E) (Set.Ico 0 T) t) :
    HasDerivAt (fun s ↦ rmNormSq (G s) x)
      (laplAt (G t) (rmNormSq (G t)) x - 2 * dRmNormSq (G t) x + 2 * qPairAt (G t) x) t := by
  have htIco : t ∈ Set.Ico 0 T := ⟨ht.1.le, ht.2⟩
  have hne : Set.Ico 0 T ∈ 𝓝 t :=
    Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) fun y hy => ⟨hy.1.le, hy.2⟩
  -- (1) the frame derivative, in the Uhlenbeck normalisation
  have hderAt : ∀ i, HasDerivAt (fun s : ℝ ↦ ((e s i : TangentSpace I x) : E))
      (((∑ j, ricAt (lcOf (G t)) x (e t i) (e t j) • e t j
        : TangentSpace I x)) : E) t := by
    intro i
    exact (hder i).hasDerivAt hne
  -- (2) the componentwise evolution, from the shared contract
  have hframe : HasDerivAt (fun s ↦ rmFrame (G s) x (e s))
      (lapRmFrame (G t) x (e t) + Q (rmFrame (G t) x (e t))) t :=
    hCE G T hflow t ht x e (fun s hs => hON s ⟨hs.1.le, hs.2⟩) hderAt
  -- (3) the chain rule for the squared Frobenius norm
  have hfrob := hasDerivAt_frobSq_comp (n := Module.finrank ℝ E) _ _ t hframe
  -- (4) identification of the derivative with the frozen right-hand side
  have hval : (∑ i, ∑ j, ∑ k, ∑ l, 2 * rmFrame (G t) x (e t) i j k l *
        (lapRmFrame (G t) x (e t) + Q (rmFrame (G t) x (e t))) i j k l)
      = laplAt (G t) (rmNormSq (G t)) x - 2 * dRmNormSq (G t) x + 2 * qPairAt (G t) x := by
    have hkato := laplAt_rmNormSq_eq_of_isONFrame hLC (G t) x (e t) (hON t htIco)
    have hq := qPairAt_eq_qPair_rmFrame hLC (G t) x (e t) (hON t htIco)
    simp only [Pi.add_apply]
    rw [sum4_two_mul_add, hkato, hq]
    simp only [qPair]
    ring
  rw [hval] at hfrob
  -- (5) transfer from `frobSq (rmFrame ...)` to `rmNormSq`, which agree near `t`
  refine hfrob.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact rmNormSq_eq_frobSq_rmFrame hLC (G s) x (e s) (hON s ⟨hs.1.le, hs.2⟩)

/-! ## The interior derivation, with the frame obtained from the Uhlenbeck existence lemma -/

theorem hasDerivAt_rmNormSq_of_CE (hLC : LCSmooth I M) (hCE : CurvEvolution I M)
    (G : ℝ → SMet I M) (T : ℝ) (hflow : IsRicciFlow G T)
    (t : ℝ) (ht : t ∈ Set.Ioo 0 T) (x : M) :
    HasDerivAt (fun s ↦ rmNormSq (G s) x)
      (laplAt (G t) (rmNormSq (G t)) x - 2 * dRmNormSq (G t) x + 2 * qPairAt (G t) x) t := by
  obtain ⟨e, hON, hder⟩ :=
    Work.Diff.GE.uhlenbeck_frame_coe hLC G T hflow t ⟨ht.1.le, ht.2⟩ x
  exact hasDerivAt_rmNormSq_of_CE_of_frame hLC hCE G T hflow t ht x e hON hder

/-! ## The endpoint `t = 0`

The identity holds on `(0,T)`; at `0` it follows by the mean-value theorem once the two sides are
known to be continuous at `0` from the right, which is `Work.Diff.GE.continuous_flow_quantities`
(a chart computation: the curvature and its derivatives along the flow are continuous). -/

theorem hasDerivWithinAt_rmNormSq_zero_of_CE (hLC : LCSmooth I M) (hCE : CurvEvolution I M)
    (G : ℝ → SMet I M) (T : ℝ) (hflow : IsRicciFlow G T) (hT : 0 < T) (x : M)
    (hcontf : ContinuousWithinAt (fun s ↦ rmNormSq (G s) x) (Set.Ico 0 T) 0)
    (hcontL : ContinuousWithinAt (fun s ↦ laplAt (G s) (rmNormSq (G s)) x
      - 2 * dRmNormSq (G s) x + 2 * qPairAt (G s) x) (Set.Ico 0 T) 0) :
    HasDerivWithinAt (fun s ↦ rmNormSq (G s) x)
      (laplAt (G 0) (rmNormSq (G 0)) x - 2 * dRmNormSq (G 0) x + 2 * qPairAt (G 0) x)
      (Set.Ico 0 T) 0 :=
  Work.Diff.GE.derivWithin_Ico_zero _ _ T hT (fun s hs => hasDerivAt_rmNormSq_of_CE hLC hCE G T hflow s hs x)
    hcontf hcontL

/-- The two continuity statements at `0⁺` needed for the endpoint.  They are a chart computation
about the frozen quantities along a jointly smooth family of metrics (see the note in the
module docstring). -/
def FlowContAtZero : Prop :=
  ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T → ∀ x : M,
    ContinuousWithinAt (fun s ↦ rmNormSq (G s) x) (Set.Ico 0 T) 0 ∧
    ContinuousWithinAt (fun s ↦ laplAt (G s) (rmNormSq (G s)) x
      - 2 * dRmNormSq (G s) x + 2 * qPairAt (G s) x) (Set.Ico 0 T) 0

theorem evol_rm_normsq_of_CE (hLC : LCSmooth I M) (hCE : CurvEvolution I M)
    (hcont : FlowContAtZero (I := I) (M := M)) :
    EvolRmNormSq I M := by
  intro G T hflow t ht x
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · subst h0
    obtain ⟨hc1, hc2⟩ := hcont G T hflow x
    exact hasDerivWithinAt_rmNormSq_zero_of_CE hLC hCE G T hflow ht.2 x hc1 hc2
  · exact (hasDerivAt_rmNormSq_of_CE hLC hCE G T hflow t ⟨hpos, ht.2⟩ x).hasDerivWithinAt

/-! ## The isolated missing input: continuity at `0⁺`

The endpoint `t = 0` of `EvolRmNormSq` needs the continuity of `s ↦ |Rm(G s)|²` and of the
right-hand side at `0⁺`.  This is a chart computation (the frozen quantities are differential
polynomials in the metric and its first derivatives, which are jointly smooth on `Ico 0 T` by
`IsRicciFlow`); it is the content of the request `Work.Diff.GE.continuous_flow_quantities`, which is
being finished in that separate module.  It is isolated here so that the rest of the assembly does
not depend on it: replace `flowContAtZero_of_isRicciFlow` by
`Work.Diff.GE.continuous_flow_quantities` when that module is complete.
-/

theorem flowContAtZero_of_isRicciFlow (hLC : LCSmooth I M) : FlowContAtZero (I := I) (M := M) :=
  Work.Diff.GE.flowContAtZero hLC

end Work.Diff.GE

/-! ## The requested lemma -/

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- **EV1: the evolution of `|Rm|²` under Ricci flow** (Hamilton 1982; Brendle–Schoen).  Under a
Ricci flow `G` on `[0,T)`, the frozen squared norm of the curvature has, at every `t ∈ [0,T)` and
every `x : M`, the within-`[0,T)` derivative
`Δ|Rm|² − 2|∇Rm|² + 2 ⟪Rm, Q(Rm)⟫`, all quantities computed with `G t`.

`CurvEvolution I M` (Hamilton's componentwise `∂ₜ R = ΔR + Q(R)` in an Uhlenbeck frame) is
discharged from the owner's `Work.Diff.Evol.curv_evolution`. -/
theorem evol_rm_normsq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : LCSmooth I M) (hLV : LCVariation I M) :
    EvolRmNormSq I M :=
  evol_rm_normsq_of_CE hLC
    (Work.Diff.Evol.curv_evolution hLC hLV (Work.Diff.Evol.curv_variation hLC hLV))
    (flowContAtZero_of_isRicciFlow hLC)

end Work.Diff.GE
