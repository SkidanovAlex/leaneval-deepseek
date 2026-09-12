import Submission.Model
import Submission.ModelCore
import Mathlib

/-!
# Uniqueness of model geodesics with prescribed initial position and velocity

Task: prove the final theorem `unique_geodesic` (replace the placeholder proof).

## Statement

For a `C³` metric family `g : E → Bilin E` (with `Bilin E := E →L[ℝ] (E →L[ℝ] ℝ)`), two
solutions of the geodesic equation (a curve + velocity pair satisfying
`HasDerivAt c (vel t) t` and `HasDerivAt vel (accel (g (c t)) (fderiv ℝ g (c t)) (vel t)) t`
on a common open interval) with the same value at `0` agree everywhere on that interval.

## Available facts (this Mathlib snapshot)

* First order reformulation: `z := (c, vel) : ℝ → E × E` satisfies
  `HasDerivAt z (odeField g (z t)) t` where `odeField g z = (z.2, accel (g z.1) (fderiv ℝ g z.1) z.2)`
  (see `Submission/Model.lean`).  From `HasDerivAt c (vel t) t` and
  `HasDerivAt vel (...) t`, prove `HasDerivAt (fun s => (c s, vel s)) (odeField g (c t, vel t)) t`
  via `HasDerivAt.prodMk`-style pairing and `simp [odeField]`.
* Local Lipschitzness: `ContDiffAt ℝ 1 (odeField g) z₀` (from
  `Submission.ModelCore.odeField_contDiffAt`) gives, via
  `ContDiffAt.exists_lipschitzOnWith`, a `K` and a ball around `z₀` on which `odeField g` is
  `K`-Lipschitz.
* Uniqueness theorems in `Mathlib/Analysis/ODE/ExistUnique.lean`:
  `ODE_solution_unique_of_mem_Icc_right` (and `_left`) — these need the RHS `v t` to be
  `LipschitzOnWith K (v t) (s t)` for `t` in a half-open interval, with both solutions
  continuous on an `Icc` and satisfying `HasDerivWithinAt` with the RHS, and contained in `s t`.

## Suggested proof strategy

1. First prove a local uniqueness lemma: for `R > 0` such that `odeField g` is Lipschitz on
   `closedBall z₀ R` with constant `K`, any two solutions defined on `Icc 0 η` (η small, with
   images inside `closedBall z₀ R`) and equal at `0` agree on `Icc 0 η`.  Apply
   `ODE_solution_unique_of_mem_Icc_right` with `v := fun _ => odeField g`,
   `s := fun _ => closedBall z₀ R` (need `∀ t ∈ Ico 0 η, LipschitzOnWith K (odeField g) (closedBall z₀ R)`).
   The two curves must satisfy `HasDerivWithinAt ... (Icc 0 η)`-versions, obtained from their
   `HasDerivAt` by `.hasDerivWithinAt` and restricting; continuity on `Icc 0 η` from
   `HasDerivAt.continuousAt`/`continuousOn` (use `continuousOn_iff_continuous_restrict` or
   `ContinuousAt.continuousOn` style; a function with `HasDerivAt` at every point of an open
   interval is continuous on compact subintervals).
   Membership in the closed ball: choose `R` after the fact — the solution restricted to `Icc 0 η`
   is continuous on a compact set, hence bounded: use `isCompact_Icc` +
   `ContinuousOn.bddAbove`/`isBounded` facts, or pick `η` small enough that the solution stays in
   a ball of radius `r` (continuity at `0` gives a small neighbourhood on which the solution is
   within distance `r/2` of `z₀`; then choose `R` large).  Simplest robust approach: prove a
   version where the interval is chosen small (`η` small) so that *by continuity at 0* the image
   is inside any given closed ball around `z₀`.
2. Extend from a neighbourhood of `0` to the whole interval `Ioo (-ε) ε` by the standard
   open-closed argument: the set of `t` where the two solutions agree is open and closed in
   `Ioo (-ε) ε` (open: local uniqueness at the agreement point applied on a small interval around
   it; closed: continuity).  Alternatively use the two one-sided uniqueness theorems repeatedly
   on overlapping intervals `Icc u v` with `u < 0 < v`.

## Simplification hints

* To turn `HasDerivAt` into the pair form: `have hz (t) (ht : t ∈ Ioo (-ε) ε) :
    HasDerivAt (fun s => (c s, vel s)) (odeField g (c t, vel t)) t := by
      exact (hc t ht).prodMk (hv t ht) |> ...` then `simpa [odeField]`.
  Actually `HasDerivAt.prodMk` gives `HasDerivAt (fun s => (c s, vel s)) (vel t, accel ...) t`;
  then `simpa [odeField]` to rewrite the derivative as `odeField g (c t, vel t)`.
* `ODE_solution_unique_of_mem_Icc_right` signature (from ExistUnique.lean):
    (hv : ∀ t ∈ Ico a b, LipschitzOnWith K (v t) (s t))
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (v t (f t)) (Ici t) t)  -- actually check exact form
    (hfs : ∀ t ∈ Ico a b, f t ∈ s t)  ...  (ha : f a = g a) : EqOn f g (Icc a b)
  Read the file to get the exact argument order and the `Ici`/`Iic` variant `_left`.
  For `ODE_solution_unique_of_mem_Icc_right` the derivative hypothesis is on `Ici t`; solutions
  with `HasDerivAt` on an open interval containing the `Icc` automatically satisfy it.

Do NOT change the statement of `unique_geodesic`.  You may add helper lemmas.  No placeholders/`axiom`
may remain.
-/

open ContinuousLinearMap
open scoped ContDiff Topology
open Set Metric

namespace Submission.Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section

/-- Model geodesics with the same initial position and velocity agree on their common domain. -/
theorem unique_geodesic (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) {ε : ℝ} (hε : 0 < ε)
    {c₁ vel₁ c₂ vel₂ : ℝ → E}
    (hc₁ : ∀ t ∈ Ioo (-ε) ε, HasDerivAt c₁ (vel₁ t) t)
    (hv₁ : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt vel₁ (accel (g (c₁ t)) (fderiv ℝ g (c₁ t)) (vel₁ t)) t)
    (hc₂ : ∀ t ∈ Ioo (-ε) ε, HasDerivAt c₂ (vel₂ t) t)
    (hv₂ : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt vel₂ (accel (g (c₂ t)) (fderiv ℝ g (c₂ t)) (vel₂ t)) t)
    (hc0 : c₁ 0 = c₂ 0) (hv0 : vel₁ 0 = vel₂ 0) :
    (∀ t ∈ Ioo (-ε) ε, c₁ t = c₂ t) ∧ (∀ t ∈ Ioo (-ε) ε, vel₁ t = vel₂ t)  := by
  let z₁ : ℝ → E × E := fun t => (c₁ t, vel₁ t)
  let z₂ : ℝ → E × E := fun t => (c₂ t, vel₂ t)
  have hz₁ (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      HasDerivAt z₁ (odeField g (z₁ t)) t := by
    dsimp [z₁]
    exact ((hc₁ t ht).prodMk (hv₁ t ht)).congr_deriv (by simp [odeField])
  have hz₂ (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      HasDerivAt z₂ (odeField g (z₂ t)) t := by
    dsimp [z₂]
    exact ((hc₂ t ht).prodMk (hv₂ t ht)).congr_deriv (by simp [odeField])
  have hloc (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (-ε) ε) (heq : z₁ t₀ = z₂ t₀) : z₁ =ᶠ[𝓝 t₀] z₂ := by
    have hcd : ContDiffAt ℝ 1 (odeField g) (z₁ t₀) := by
      dsimp [z₁]
      exact odeField_contDiffAt g hg hinv (c₁ t₀) (vel₁ t₀)
    have hsf : HasStrictFDerivAt (odeField g) (fderiv ℝ (odeField g) (z₁ t₀)) (z₁ t₀) :=
      hcd.hasStrictFDerivAt one_ne_zero
    rcases hsf.exists_lipschitzOnWith with ⟨K, s0, hs0, hlip0⟩
    have hmem₁ : ∀ᶠ t in 𝓝 t₀, z₁ t ∈ s0 :=
      (hz₁ t₀ ht₀).continuousAt.preimage_mem_nhds hs0
    have hmem₂ : ∀ᶠ t in 𝓝 t₀, z₂ t ∈ s0 := by
      have hs0' : s0 ∈ 𝓝 (z₂ t₀) := by rwa [heq] at hs0
      exact (hz₂ t₀ ht₀).continuousAt.preimage_mem_nhds hs0'
    have hder₁ : ∀ᶠ t in 𝓝 t₀, HasDerivAt z₁ (odeField g (z₁ t)) t := by
      filter_upwards [Ioo_mem_nhds ht₀.1 ht₀.2] with t ht
      exact hz₁ t ht
    have hder₂ : ∀ᶠ t in 𝓝 t₀, HasDerivAt z₂ (odeField g (z₂ t)) t := by
      filter_upwards [Ioo_mem_nhds ht₀.1 ht₀.2] with t ht
      exact hz₂ t ht
    exact ODE_solution_unique_of_eventually (v := fun _ => odeField g) (s := fun _ => s0)
      (Filter.Eventually.of_forall (fun _ => hlip0)) (hder₁.and hmem₁) (hder₂.and hmem₂) heq
  have hz0 : z₁ 0 = z₂ 0 := by
    dsimp [z₁, z₂]
    exact Prod.ext hc0 hv0
  have h0mem : (0 : ℝ) ∈ Ioo (-ε) ε := by constructor <;> linarith
  set u : Set ℝ := {t | z₁ t = z₂ t} ∩ Ioo (-ε) ε
  have hu_open : IsOpen u := by
    rw [isOpen_iff_mem_nhds]
    intro t₁ ht₁
    have ht₁ag : z₁ t₁ = z₂ t₁ := ht₁.1
    have ht₁I : t₁ ∈ Ioo (-ε) ε := ht₁.2
    have heq_t₁ : z₁ =ᶠ[𝓝 t₁] z₂ := hloc t₁ ht₁I ht₁ag
    apply (heq_t₁.and (Ioo_mem_nhds ht₁I.1 ht₁I.2)).mono
    intro t ht
    exact ⟨ht.1, ht.2⟩
  have hu_nonempty : (Ioo (-ε) ε ∩ u).Nonempty := by
    refine ⟨0, h0mem, ?_⟩
    exact ⟨hz0, h0mem⟩
  have hu_closed : closure u ∩ Ioo (-ε) ε ⊆ u := by
    intro t ht
    have htI : t ∈ Ioo (-ε) ε := ht.2
    have htAg : z₁ t = z₂ t := by
      by_contra hne
      rcases t2_separation hne with ⟨U, V, hUo, hVo, hxU, hxV, hUV⟩
      have hpre1 : z₁ ⁻¹' U ∈ 𝓝 t :=
        (hz₁ t htI).continuousAt.preimage_mem_nhds (hUo.mem_nhds hxU)
      have hpre2 : z₂ ⁻¹' V ∈ 𝓝 t :=
        (hz₂ t htI).continuousAt.preimage_mem_nhds (hVo.mem_nhds hxV)
      let W : Set ℝ := z₁ ⁻¹' U ∩ z₂ ⁻¹' V
      have hW : W ∈ 𝓝 t := Filter.inter_mem hpre1 hpre2
      have hUVempty : U ∩ V = ∅ := by
        simpa [Set.disjoint_iff] using hUV
      have hWu : W ∩ u = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro s hs
        have hsW : s ∈ W := hs.1
        have hsu : s ∈ u := hs.2
        have hmemU : z₁ s ∈ U := hsW.1
        have hmemV : z₂ s ∈ V := hsW.2
        have hEq : z₁ s = z₂ s := hsu.1
        have hmemV' : z₁ s ∈ V := by simpa [hEq] using hmemV
        have hx : z₁ s ∈ U ∩ V := ⟨hmemU, hmemV'⟩
        rw [hUVempty] at hx
        simp at hx
      rcases (_root_.mem_nhds_iff.mp hW) with ⟨O, hOW, hOo, htO⟩
      have hclO : (O ∩ u).Nonempty := (_root_.mem_closure_iff.mp ht.1) O hOo htO
      have hOempty : O ∩ u = ∅ := by
        have hsubW : O ∩ u ⊆ W ∩ u := inter_subset_inter_left u hOW
        rw [hWu] at hsubW
        exact subset_empty_iff.mp hsubW
      rw [hOempty] at hclO
      exact not_nonempty_empty hclO
    exact ⟨htAg, htI⟩
  have hsub : Ioo (-ε) ε ⊆ u := by
    exact isPreconnected_Ioo.subset_of_closure_inter_subset (s := Ioo (-ε) ε) (u := u)
      hu_open hu_nonempty hu_closed
  have hzeq : ∀ t ∈ Ioo (-ε) ε, z₁ t = z₂ t := fun t ht => (hsub ht).1
  refine ⟨?_, ?_⟩
  · intro t ht
    have hz := hzeq t ht
    dsimp [z₁, z₂] at hz
    exact congrArg Prod.fst hz
  · intro t ht
    have hz := hzeq t ht
    dsimp [z₁, z₂] at hz
    exact congrArg Prod.snd hz

end

end Submission.Model
