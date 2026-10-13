/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EpsE4Thr/BarrierIco.lean` — the barrier lemmas with **one-sided** continuity

`Work.FTS.Apriori.barrier_within` is the engine of the level-four a-priori bound: it needs the
energy `E` to be *continuous on the closed interval* `[0,T]`, and a strictly negative
within-derivative at every time at which `E` meets the barrier level `Y`.  The hypotheses the
route can actually supply are weaker:

* the identity `HasDerivWithinAt E (E4' τ) (Set.Icc 0 T') τ` is available at every **interior**
  fake time (`DiagCurveISolution.EnergyDeriv_IP4_JfamP_of_solution`, valid for `τ ∈ Ioo 0 T`), and
  `HasDerivWithinAt` gives continuity *at that point* for free;
* nothing is known about `E` to the *right* of `T'`, so `ContinuousOn E (Icc 0 T')` is not
  derivable (the value at `T'` from the right is free — session 4's counterexample).

This module removes the global-continuity hypothesis completely:

* `continuousOn_Ico_of_hasDerivWithinAt` — a within-derivative on `Icc 0 T` at every
  `τ ∈ Ico 0 T` gives `ContinuousOn E (Ico 0 T)`;
* `barrier_within_Ico` — the barrier on the **half-open** interval, with the continuity hypothesis
  `ContinuousOn E (Ico 0 T)` (which the previous lemma derives from `hderiv` alone); the proof is a
  reduction to `barrier_within` on the subinterval `[0, (τ+T)/2]`, which is contained in `Ico 0 T`;
* `barrier_within_Icc_of_hasDerivWithinAt` — the same, on `Icc 0 T`, at the price of the **single
  endpoint** hypothesis `ContinuousWithinAt E (Icc 0 T) T` (a left limit at `T`, which is the only
  information the closed-interval statement needs beyond the half-open one).

The payoff for the level-four chapter: the `hcont` input of `apriori_fourth_of_transfer` is
reduced from "continuity on the whole closed interval" to "one left limit at `T'`", while
`hderiv` (already available from the proved energy identity) supplies everything else.  The same
reduction applies verbatim to the level-six Grönwall barrier
(`energy_barrier_Ico`/`energy_barrier_endpoint`).

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.Apriori.Barrier

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Continuity on `Ico 0 T` from a within-derivative on `Icc 0 T`.**

At an interior point of `Icc 0 T` a `HasDerivWithinAt` on `Icc 0 T` is an honest derivative, hence
gives continuity; and continuity within `Icc 0 T` restricts to continuity within the smaller set
`Ico 0 T`.  So the (one-sided) derivative information alone yields continuity on the half-open
interval — which is exactly what the barrier needs. -/
theorem continuousOn_Ico_of_hasDerivWithinAt {E E' : ℝ → ℝ} {T : ℝ}
    (h : ∀ τ ∈ Set.Ico 0 T, HasDerivWithinAt E (E' τ) (Set.Icc 0 T) τ) :
    ContinuousOn E (Set.Ico 0 T) :=
  fun τ hτ => (h τ hτ).continuousWithinAt.mono fun _ hx => ⟨hx.1, le_of_lt hx.2⟩

/-- **The barrier lemma on the half-open interval.**  If `E` is continuous on `Ico 0 T`, starts
below `Y`, and has a strictly negative within-`Icc 0 T`-derivative at every `τ ∈ Ico 0 T` at which
`E τ = Y`, then `E` never exceeds `Y` on `Ico 0 T`.

Proof: for `τ ∈ Ico 0 T` apply `Work.FTS.Apriori.barrier_within` on the *subinterval*
`[0, (τ+T)/2]`.  All its hypotheses transfer because `Icc 0 ((τ+T)/2) ⊆ Ico 0 T`. -/
theorem barrier_within_Ico {E E' : ℝ → ℝ} {Y T : ℝ} (hT : 0 < T)
    (hcont : ContinuousOn E (Set.Ico 0 T))
    (hderiv : ∀ τ ∈ Set.Ico 0 T, HasDerivWithinAt E (E' τ) (Set.Icc 0 T) τ)
    (h0 : E 0 < Y)
    (hneg : ∀ τ ∈ Set.Ico 0 T, E τ = Y → E' τ < 0) :
    ∀ τ ∈ Set.Ico 0 T, E τ ≤ Y := by
  intro τ hτ
  have hτT : τ < T := hτ.2
  set T' : ℝ := (τ + T) / 2 with hT'def
  have hT'T : T' < T := by rw [hT'def]; linarith
  have hτT' : τ ≤ T' := by rw [hT'def]; linarith
  have hsub : Set.Icc 0 T' ⊆ Set.Ico 0 T :=
    fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hT'T⟩
  have hsubD : Set.Icc 0 T' ⊆ Set.Icc 0 T := Set.Icc_subset_Icc_right (le_of_lt hT'T)
  exact Work.FTS.Apriori.barrier_within (E := E) (E' := E') (Y := Y) (T := T')
    (hcont.mono hsub) h0
    (fun s hs => (hderiv s (hsub ⟨hs.1, le_of_lt hs.2⟩)).mono hsubD)
    (fun s hs => hneg s (hsub ⟨hs.1, le_of_lt hs.2⟩))
    τ ⟨hτ.1, hτT'⟩

/-- **The barrier lemma on the half-open interval, with the continuity derived from the
derivative.**  Same as `barrier_within_Ico`, with the continuity hypothesis dropped: it is
`continuousOn_Ico_of_hasDerivWithinAt`.  This is the form the level-four chapter consumes, since the
proved energy identity supplies `hderiv` and nothing else. -/
theorem barrier_within_Ico_of_hasDerivWithinAt {E E' : ℝ → ℝ} {Y T : ℝ} (hT : 0 < T)
    (hderiv : ∀ τ ∈ Set.Ico 0 T, HasDerivWithinAt E (E' τ) (Set.Icc 0 T) τ)
    (h0 : E 0 < Y)
    (hneg : ∀ τ ∈ Set.Ico 0 T, E τ = Y → E' τ < 0) :
    ∀ τ ∈ Set.Ico 0 T, E τ ≤ Y :=
  barrier_within_Ico hT (continuousOn_Ico_of_hasDerivWithinAt hderiv) hderiv h0 hneg

/-- **The barrier lemma on the closed interval, with a one-sided endpoint hypothesis.**

Same as `barrier_within_Ico`, with the conclusion extended to `τ = T` at the price of the single
additional hypothesis `ContinuousWithinAt E (Icc 0 T) T` (the left limit of `E` at `T`).  The
sequence `T - min (T/2) (1/(n+1))` lies in `Ico 0 T` for every `n`, tends to `T`, so
`le_of_tendsto_of_tendsto` gives `E T ≤ Y`. -/
theorem barrier_within_Icc_of_hasDerivWithinAt {E E' : ℝ → ℝ} {Y T : ℝ} (hT : 0 < T)
    (hderiv : ∀ τ ∈ Set.Ico 0 T, HasDerivWithinAt E (E' τ) (Set.Icc 0 T) τ)
    (h0 : E 0 < Y)
    (hneg : ∀ τ ∈ Set.Ico 0 T, E τ = Y → E' τ < 0)
    (hcontT : ContinuousWithinAt E (Set.Icc 0 T) T) :
    ∀ τ ∈ Set.Icc 0 T, E τ ≤ Y := by
  have hIco : ∀ τ ∈ Set.Ico 0 T, E τ ≤ Y :=
    barrier_within_Ico hT (continuousOn_Ico_of_hasDerivWithinAt hderiv) hderiv h0 hneg
  intro τ hτ
  rcases lt_or_eq_of_le hτ.2 with h | h
  · exact hIco τ ⟨hτ.1, h⟩
  · rw [h]
    set u : ℕ → ℝ := fun n => T - min (T / 2) (1 / ((n : ℝ) + 1)) with hudef
    have hsmall : ∀ n : ℕ, 0 < min (T / 2) (1 / ((n : ℝ) + 1)) := fun n =>
      lt_min (by linarith) (by positivity)
    have hleT : ∀ n : ℕ, min (T / 2) (1 / ((n : ℝ) + 1)) ≤ T / 2 := fun n => min_le_left _ _
    have hu_lt : ∀ n : ℕ, u n < T := by
      intro n; simp only [u]; linarith [hsmall n]
    have hu_ge : ∀ n : ℕ, 0 ≤ u n := by
      intro n; simp only [u]; linarith [hleT n, hT]
    have hmin_tendsto : Tendsto (fun n : ℕ => min (T / 2) (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 : Tendsto (fun _ : ℕ => T / 2) atTop (𝓝 (T / 2)) := tendsto_const_nhds
      have h3 : Tendsto (fun n : ℕ => min (T / 2) (1 / ((n : ℝ) + 1))) atTop
          (𝓝 (min (T / 2) (0 : ℝ))) := h2.min h1
      simpa [min_eq_right (by linarith : (0 : ℝ) ≤ T / 2)] using h3
    have hu_tendsto : Tendsto u atTop (𝓝 T) := by
      have h4 : Tendsto (fun n : ℕ => T - min (T / 2) (1 / ((n : ℝ) + 1))) atTop
          (𝓝 (T - 0)) := tendsto_const_nhds.sub hmin_tendsto
      simpa [u] using h4
    have hu_nhds : Tendsto u atTop (𝓝[Set.Icc 0 T] T) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hu_tendsto, Filter.Eventually.of_forall fun n => ⟨hu_ge n, (hu_lt n).le⟩⟩
    have hEseq : Tendsto (fun n : ℕ => E (u n)) atTop (𝓝 (E T)) := hcontT.tendsto.comp hu_nhds
    have hle : ∀ᶠ n in atTop, E (u n) ≤ Y :=
      Filter.Eventually.of_forall fun n => hIco (u n) ⟨hu_ge n, hu_lt n⟩
    exact le_of_tendsto_of_tendsto hEseq tendsto_const_nhds hle

end Work.FTS.StrongEps.EpsE4Thr
