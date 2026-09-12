import Submission.Model
import Submission.ModelCore
import Mathlib

/-!
# The model geodesic flow is Lipschitz in the initial data

Task: prove the final theorem `flow_lipschitz`.

## Statement (in words)

For a `C³` metric family `g : E → Bilin E` (with `Bilin E := E →L[ℝ] (E →L[ℝ] ℝ)`) whose
values are all invertible, around any `(x₀, v₀) : E × E` there is a radius `r > 0` and a time
`T > 0` such that for every `t ∈ Icc (-T) T` the geodesic-flow map
`(x, v) ↦ (position at time t, velocity at time t)` is Lipschitz on the closed ball
`closedBall (x₀, v₀) r` (with a Lipschitz constant independent of `t`).

## Available facts (this Mathlib snapshot, `Mathlib/Analysis/ODE/`)

* `IsPicardLindelof.of_contDiffAt_one` (in `PicardLindelof.lean`):
    {f : E → E} {x₀ : E} (hf : ContDiffAt ℝ 1 f x₀) :
      ∃ (ε : ℝ) (hε : 0 < ε) (a r L K : ℝ≥0) (_ : 0 < r),
        ∀ (t₀ : ℝ), IsPicardLindelof (fun _ => f)
          (tmin := t₀ - ε) (tmax := t₀ + ε) ⟨t₀, by simp [le_of_lt hε]⟩ x₀ a r L K
  Apply it to `f := odeField g` at `(x₀, v₀)`, using
  `Submission.ModelCore.odeField_contDiffAt g hg hinv x₀ v₀` for ContDiffAt ℝ 1 (odeField g) (x₀,v₀).
* `IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith`:
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
      ∃ α : E → ℝ → E, (∀ x ∈ closedBall x₀ r, α x t₀ = x ∧
        ∀ t ∈ Icc tmin tmax, HasDerivWithinAt (α x) (f t (α x t)) (Icc tmin tmax) t) ∧
        ∃ L' : ℝ≥0, ∀ t ∈ Icc tmin tmax, LipschitzOnWith L' (α · t) (closedBall x₀ r)
  (Here `E` plays the role of `E × E` in our setting; the vector field is time-independent so
  `f t = f`.)
* `IsPicardLindelof.shrink_time` and `.shrink` let you recentre the time interval at `0` and
  shrink it so that `tmin = -T, tmax = T` around `t₀ = 0`.

## Output form

Concretely prove:

    ∃ r > 0, ∃ T > 0, ∃ L : ℝ≥0,
      ∀ t ∈ Icc (-T) T, ∀ z₁ ∈ closedBall (x₀, v₀) r, ∀ z₂ ∈ closedBall (x₀, v₀) r,
        let (c₁, vel₁) := (α z₁ t)   -- you choose how to store the flow
        dist z-flow...   -- state as you like, see below

Because solutions are pairs, it is cleanest to phrase the theorem with an explicit flow map
`Φ : E × E → ℝ → E × E` (defined on the ball): `Φ z 0 = z`, derivative conditions, and
`LipschitzOnWith L (fun z => Φ z t) (closedBall (x₀, v₀) r)` for each `t ∈ Icc (-T) T`.
Use `t₀ := 0` and the `shrink_time` lemma to make the interval symmetric around 0.

## Recommended concrete statement to prove (keep this signature; helper lemmas allowed)

    theorem flow_lipschitz (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
        (hinv : ∀ x, (g x).IsInvertible) (x₀ v₀ : E) :
        ∃ r > 0, ∃ T > 0, ∃ L : NNReal, ∃ Φ : E × E → ℝ → E × E,
          (∀ z ∈ closedBall (x₀, v₀) r, Φ z 0 = z ∧
             ∀ t ∈ Icc (-T) T,
               HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
          (∀ t ∈ Icc (-T) T, LipschitzOnWith L (fun z => Φ z t) (closedBall (x₀, v₀) r))

(Getting `HasDerivAt` on the whole interval from `HasDerivWithinAt` on `Icc (-T) T` is fine for
`t ∈ Ioo (-T) T`, which is enough; state the derivative condition only for `t ∈ Ioo (-T) T` if
that is easier, and keep Lipschitz on `Icc`.)

Do NOT change the statement of `flow_lipschitz`.  You may add helper lemmas.
-/

open ContinuousLinearMap
open scoped ContDiff Topology
open Set Metric

namespace Submission.Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section

/-- The geodesic flow is locally Lipschitz in the initial data, uniformly on a symmetric time
interval around `0`. -/
theorem flow_lipschitz (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ v₀ : E) :
    ∃ r > 0, ∃ T > 0, ∃ L : NNReal, ∃ Φ : E × E → ℝ → E × E,
      (∀ z ∈ closedBall (x₀, v₀) r, Φ z 0 = z ∧
         ∀ t ∈ Icc (-T) T,
           HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
      (∀ t ∈ Icc (-T) T, LipschitzOnWith L (fun z => Φ z t) (closedBall (x₀, v₀) r)) := by
  have hF : ContDiffAt ℝ 1 (odeField g) (x₀, v₀) := odeField_contDiffAt g hg hinv x₀ v₀
  -- Picard-Lindelöf parameters for the C¹ time-independent field `odeField g : E × E → E × E`.
  rcases IsPicardLindelof.of_contDiffAt_one (E := E × E) (f := odeField g)
      (x₀ := (x₀, v₀)) hF with ⟨ε, hε, a, r₀, L₀, K₀, hr₀, hPL⟩
  -- Local flow obtained from the Picard-Lindelöf theorem, centred at time 0 and defined on the
  -- closed interval `Icc (0 - ε) (0 + ε)` for all initial data in `closedBall (x₀, v₀) r₀`.
  obtain ⟨α, hα, L₁, hLip⟩ :=
    IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
      (E := E × E) (hPL 0)
  -- Shrink the time interval so that its closed interval lies strictly inside the open interval
  -- `Ioo (0 - ε) (0 + ε)`; at every such time the derivative below is an honest `HasDerivAt`.
  let T : ℝ := ε / 2
  have hT : 0 < T := by
    dsimp [T]
    exact div_pos hε zero_lt_two
  have hTε : T < ε := by
    dsimp [T]
    exact half_lt_self hε
  refine ⟨(r₀ : ℝ), ?_, T, hT, L₁, (fun z => α z), ?_, ?_⟩
  · exact_mod_cast hr₀
  · intro z hz
    constructor
    · simpa using (hα z hz).1
    · intro t ht
      have h1 : -T ≤ t := (mem_Icc.mp ht).1
      have h2 : t ≤ T := (mem_Icc.mp ht).2
      have htlo : 0 - ε < t := by linarith
      have hthi : t < 0 + ε := by linarith
      have htIcc : t ∈ Icc (0 - ε) (0 + ε) := by
        constructor <;> linarith
      exact ((hα z hz).2 t htIcc).hasDerivAt (Icc_mem_nhds htlo hthi)
  · intro t ht
    have h1 : -T ≤ t := (mem_Icc.mp ht).1
    have h2 : t ≤ T := (mem_Icc.mp ht).2
    exact hLip t (by constructor <;> linarith)

end

end Submission.Model
