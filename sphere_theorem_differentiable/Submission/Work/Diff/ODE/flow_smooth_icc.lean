import Mathlib
import Submission.Diff.ODE
import Submission.Work.Diff.EXT.covK_onFrameFamily
import Submission.Work.Diff.ODE.exists_localExt_at
import Submission.Work.Diff.ODE.exists_global_ext_of_finite_cover

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

CONTEXT: this is one area of the Brendle–Schoen differentiable sphere theorem, driven by the lead. Read HANDOFF.md.
The contracts in Submission/Diff/Interfaces.lean and Submission/Diff/Alg.lean are frozen. Your statement's hypotheses are other
areas' contracts: USE them, do not re-prove them. Go wide: file all the independent sub-lemmas at once,
each with an exact statement, and write your assembly against their statements. If your statement looks
false or unprovable as stated, say so at once in `declare_false` with a precise reason. The lead will fix it.
ROUTE. The field is smooth only on [a,b] × M (within), e.g. a DeTurck field smooth up to t = 0 from the right. Two options:
(A) Extension. Extend X to a jointly smooth field on ℝ × M (Seeley's extension in the t variable, chart-wise, or
    via Borel's lemma for the t-jets at a and b plus the flat-function trick). Apply hFlow (the global SmoothFlow, proved by
    Diff/ODE/flow_smooth) to the extension and restrict. The flow on [a,b]² depends only on X on [a,b] (uniqueness).
    Within-derivatives follow from the global ones.
(B) Direct. Clamp: X̃(t) = X(clamp t). It is continuous in t and smooth in x. Redo the flow-box argument of
    Submission/Work/Diff/ODE/flow_smooth.lean with t-continuous fields, then get the within-t smoothness from the equation.
(A) is recommended: Seeley's extension is a standalone real-analysis lemma (a function on [0,∞) smooth up to 0 extends to a
    smooth function on ℝ) plus parameters. Seeley: f(−t) := Σ a_k φ(2^k t) f(2^k t) with Σ a_k(−2^k)^j = 1 for all j.
    The simpler Borel-jets version: take the one-sided jets at 0, a Borel function g with those jets, and define the extension as
    g on t < 0. It is smooth because all one-sided jets agree. Pick one route and state it cleanly.

## Implementation (route (A), completed)

`SmoothFlowIcc` asks, for a field `X` that is only *jointly smooth on the closed slab* `[a,b] × M`
(`Work.Diff.EXT.JointField X (Icc a b ×ˢ univ)`), for a flow that is jointly smooth on
`([a,b] × [a,b]) × M` and solves the ODE on the closed time interval.

The proof extends `X` to a *globally* jointly smooth field `Xg` on `ℝ × M` agreeing with `X` on the
slab, and then applies the global contract `SmoothFlow` (`hFlow`) to `Xg`; the flow of `Xg`
restricted to `[a,b]²` is the required flow of `X` (its flow lines only see `Xg` at times in
`[a,b]`, where `Xg = X`).

The construction of `Xg` is in two steps, each delegated:

* `Work.Diff.ODE.exists_localExt_at` — *local* extension at every point `(t₀, x₀)` of the slab:
  there are an open `V ∋ (t₀, x₀)` and a field `G`, jointly smooth on `V`, equal to `X` on
  `V ∩ ([a,b] × M)`. In the interior of the slab this is trivial; at the endpoints `t₀ = a`, `t₀ = b`
  it is the one-sided ("Seeley") extension of the chart field `chartField X x₀` from the half slab
  `{t₀ ≤ t}` resp. `{t ≤ t₀}` — Mathlib-side engine: `Work.Diff.EXT.local_ext_of_within`
  (a function `C^∞` on `Ico 0 T × U` extends to `Ioo (-ε) ε × V`), read back through the
  tangent-bundle trivialisation using `Work.Diff.EXT.jointField_iff_coords`.
* `Work.Diff.ODE.exists_global_ext_of_finite_cover` — gluing the local pieces: a finite cover of
  the compact slab by such `V`'s, a smooth partition of unity, and a bump function cutting off
  outside the slab produce a globally jointly smooth `Xg` with `Xg = X` on the slab.

Both ingredients are sorry-free; only `hFlow` (the contract `Submission.Diff.SmoothFlow`, which the
ODE area proves in `Submission/Work/Diff/ODE/flow_smooth.lean`) is used as a hypothesis.
-/

namespace Work.Diff.ODE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

theorem flow_smooth_icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hFlow : SmoothFlow I M) :
    SmoothFlowIcc I M := by
  intro a b X hab hX
  -- ### Step 1: at every point of the slab, a local jointly smooth extension agreeing on the slab
  have hKc : IsCompact (Icc a b ×ˢ (univ : Set M)) := isCompact_Icc.prod isCompact_univ
  have key : ∀ p : ↥(Icc a b ×ˢ (univ : Set M)),
      ∃ V : Set (ℝ × M), IsOpen V ∧ (p : ℝ × M) ∈ V ∧
        ∃ G : ℝ → Π x : M, TangentSpace I x,
          Work.Diff.EXT.JointField G V ∧ ∀ q ∈ V, q.1 ∈ Icc a b → G q.1 q.2 = X q.1 q.2 :=
    fun p => exists_localExt_at (X := X) (a := a) (b := b) hab hX p.2.1 (p : ℝ × M).2
  choose Vf hVopen hpV Gf hGf hagrf using key
  -- ### Step 2: finitely many of them cover the (compact) slab
  have hcov : (Icc a b ×ˢ (univ : Set M)) ⊆ ⋃ p : ↥(Icc a b ×ˢ (univ : Set M)), Vf p :=
    fun q hq => mem_iUnion.mpr ⟨⟨q, hq⟩, hpV ⟨q, hq⟩⟩
  obtain ⟨s, hs⟩ := hKc.elim_finite_subcover Vf (fun p => hVopen p) hcov
  -- ### Step 3: glue them into a globally smooth field `Xg` agreeing with `X` on the slab
  obtain ⟨Xg, hXg, hagrX⟩ :=
    exists_global_ext_of_finite_cover (I := I) (M := M) (X := X) hab s Vf Gf
      (fun i _ => hVopen i) (fun i _ => hGf i) hs
      (fun i _ q hq hqab => hagrf i q hq hqab)
  -- ### Step 4: apply the global flow contract to `Xg` and restrict to `[a,b]² × M`
  have hXg' : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M => (⟨p.2, Xg p.1 p.2⟩ : TangentBundle I M)) :=
    fun x => (hXg x (mem_univ x)).contMDiffAt Filter.univ_mem
  obtain ⟨Φ, hΦsm, hΦ0, hΦcomp, hΦode⟩ := hFlow Xg hXg'
  refine ⟨Φ, ?_, ?_, ?_, ?_⟩
  · intro q _
    exact (hΦsm q).contMDiffWithinAt
  · intro s' _ x
    exact hΦ0 s' x
  · intro s' _ t _ u _ x
    exact hΦcomp s' t u x
  · intro s' _ t ht x
    have h1 : Xg t = X t := funext (hagrX t ht)
    have h2 := (hΦode s' t x).hasMFDerivWithinAt (s := Icc a b)
    rw [h1] at h2
    exact h2

end Work.Diff.ODE
