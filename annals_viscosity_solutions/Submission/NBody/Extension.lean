import ChallengeDeps
import Submission.NBody.Bridge
import Submission.Commons.Analysis.ODE.exists_extension_of_tendsto_atRight
import Submission.Commons.Analysis.ODE.limit_at_right_of_lipschitzOnWith_of_lt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Continuation of solutions of the `N`-body flow

The local flow of Newton's equations is only limited by collisions: as long as the state
`(x, v)` tends to a limit whose position is collision-free, the solution can be continued past
the end of its interval of existence.

We record the two forms of this fact used downstream:

* `exists_extension_stateField`: extension past any time `b` at which the state has a
  collision-free limit;
* `exists_extension_of_confined_compact`: a solution which is confined, near the endpoint `T` of
  its interval, to a *compact* set of collision-free configurations extends past `T`.  This is
  the form of the statement needed to run the "escape from compact sets" argument in Chazy's
  lemma.

Everything here is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators
open scoped Topology

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- The state field is continuous on the open set of collision-free configurations. -/
lemma continuousOn_stateField (m : Fin N → ℝ) :
    ContinuousOn (stateField m) {z : EN E N × EN E N | WithoutCollisions z.1} := by
  have h1 : ContinuousOn (fun z : EN E N × EN E N => z.2) {z | WithoutCollisions z.1} :=
    continuous_snd.continuousOn
  have h2 : ContinuousOn (fun z : EN E N × EN E N => weightedGrad m (U m) z.1)
      {z | WithoutCollisions z.1} :=
    ((contDiffOn_weightedGrad_U m).continuousOn).comp continuous_fst.continuousOn (fun z hz => hz)
  exact h1.prodMk h2

/-- **Continuation past a collision-free limit.**  If `z` solves the state equation on `(a, b)`
and has a limit `l` with collision-free position at `b⁻`, then `z` extends to a solution on
`(a, b + δ)` for some `δ > 0`. -/
theorem exists_extension_stateField (m : Fin N → ℝ) {a b : ℝ} (hab : a < b)
    {z : ℝ → EN E N × EN E N} {l : EN E N × EN E N}
    (hz : ∀ t ∈ Ioo a b, HasDerivAt z (stateField m (z t)) t)
    (hlim : Tendsto z (𝓝[<] b) (𝓝 l)) (hl : WithoutCollisions l.1) :
    ∃ δ > (0 : ℝ), ∃ w : ℝ → EN E N × EN E N,
      (∀ t ∈ Ioo a (b + δ), HasDerivAt w (stateField m (w t)) t) ∧ EqOn w z (Ioo a b) :=
  Commons.Analysis.ODE.exists_extension_of_tendsto_atRight hab
    (contDiffAt_stateField m l.1 l.2 hl) hz hlim

/-- **Escape from compact sets.**  A solution of the state equation on `(a, T)`, whose trajectory
is confined near `T` to a compact set of collision-free configurations, extends past `T`. -/
theorem exists_extension_of_confined_compact (m : Fin N → ℝ) {a c T : ℝ} (hac : a < c)
    (hcT : c < T) {z : ℝ → EN E N × EN E N}
    (hz : ∀ t ∈ Ioo a T, HasDerivAt z (stateField m (z t)) t)
    {K : Set (EN E N × EN E N)} (hK : IsCompact K) (hKnc : K ⊆ {z | WithoutCollisions z.1})
    (hconf : ∀ t ∈ Ioo c T, z t ∈ K) :
    ∃ δ > (0 : ℝ), ∃ w : ℝ → EN E N × EN E N,
      (∀ t ∈ Ioo a (T + δ), HasDerivAt w (stateField m (w t)) t) ∧ EqOn w z (Ioo a T) := by
  have hcTmem : (c + T) / 2 ∈ Ioo c T := ⟨by linarith, by linarith⟩
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn ((continuousOn_stateField m).mono hKnc)
  have hM0 : (0 : ℝ) ≤ M :=
    le_trans (norm_nonneg _) (hM _ (hconf _ hcTmem))
  have hdiff : ∀ t ∈ Ioo c T, HasDerivAt z (stateField m (z t)) t :=
    fun t ht => hz t ⟨lt_trans hac ht.1, ht.2⟩
  have hbound : ∀ t ∈ Ioo c T, ‖stateField m (z t)‖ ≤ M :=
    fun t ht => hM _ (hconf t ht)
  have hlip : LipschitzOnWith ⟨M, hM0⟩ z (Ioo c T) :=
    Convex.lipschitzOnWith_of_nnnorm_deriv_le (s := Ioo c T) (f := z) (C := ⟨M, hM0⟩)
      (fun t ht => (hdiff t ht).differentiableAt)
      (fun t ht => by rw [(hdiff t ht).deriv]; exact_mod_cast hbound t ht) (convex_Ioo c T)
  obtain ⟨l, hl⟩ := Commons.Analysis.ODE.limit_at_right_of_lipschitzOnWith_of_lt hcT hlip
  have hlK : l ∈ K := by
    refine hK.isClosed.mem_of_tendsto hl ?_
    filter_upwards [Ioo_mem_nhdsLT hcT] with t ht
    exact hconf t ht
  exact exists_extension_stateField m (lt_trans hac hcT) hz hl (hKnc hlK)

end Submission.NBody
