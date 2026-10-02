import Mathlib
import Submission.Work.RatHurewicz.trackSetup
import Submission.Work.StemsB.HurewiczFibration
import Submission.Work.StemsB.isSerreFibration_evalOne

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The mapping track of a map is a Hurewicz fibration

For a continuous map `inc : X → Z`, `Work.RatHurewicz.Track inc`
(`Submission/Work/RatHurewicz/trackSetup.lean`) is the space of pairs `(x, γ)` with `γ` a path in
`Z` *ending* at `inc x`, and `Work.RatHurewicz.trackMap inc : Track inc → Z` is `(x,γ) ↦ γ 0`.
This file proves that `trackMap inc` is a **Hurewicz fibration**, i.e. that it has the homotopy
lifting property with respect to every test space.

This is the classical "mapping path/track fibration" of `inc`, in the form in which
`Work.RatHurewicz.truncationHomologyTransfer_of_serre` needs it: the track models the pair
`(X, F)` of `inc`, with `F` its homotopy fibre.

## The lift

Let `f : W → Track inc` be written `f w = (x w, γ_w)` and let `H : I × W → Z` be a homotopy of
`trackMap ∘ f`, so `H (0, w) = γ_w 0`.  The lifted homotopy at time `s` and space variable `w` is
the point of `Track inc` whose first coordinate is `x w` and whose path is

`t ↦ if t ≤ s/2 then H (s - 2t, w) else γ_w ((t - s/2)/(1 - s/2))`,

i.e. the path *doubles back* along `H (·, w)` from time `s` to time `0` and then continues along
`γ_w` from `γ_w 0 = H (0, w)` to `γ_w 1 = inc (x w)`.  The two branches agree at the junction
`t = s/2` — both are `H (0, w) = γ_w 0` — which is what makes the piecewise definition continuous
(Mathlib's `Continuous.if_le`, exactly as in the proof that the path–loop fibration is a Hurewicz
fibration, `Work.StemsB.hasHLP_evalOne`).  At `t = 1` the path ends at `γ_w 1 = inc (x w)`, so the
point really lies in `Track inc`; at `s = 0` the lifted point is `f w` again; and the value of
`trackMap` on it is the path's value at `t = 0`, which is `H (s, w)`.

## Main declarations

* `Work.RatHurewicz.hasHLP_trackMap` — the HLP of `trackMap inc` with respect to one test space.
* `Work.RatHurewicz.isHurewiczFibration_trackMap` — `trackMap inc` is a Hurewicz fibration.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

universe u

variable {X Z : Type u} [TopologicalSpace X] [TopologicalSpace Z]

/-- **The homotopy lifting property of the mapping-track map.**  The map
`trackMap inc : Track inc → Z`, `(x,γ) ↦ γ 0`, has the homotopy lifting property with respect to an
arbitrary test space `W`. -/
theorem hasHLP_trackMap (inc : C(X, Z)) (W : Type*) [TopologicalSpace W] :
    Work.StemsB.HasHLP (trackMap inc) W := by
  classical
  intro f b H
  -- the two components of the track point `f w`
  have hxcont : Continuous fun w : W => (f w).1.1 :=
    continuous_fst.comp (continuous_subtype_val.comp f.continuous)
  have hpcont : Continuous fun w : W => (f w).1.2 :=
    continuous_snd.comp (continuous_subtype_val.comp f.continuous)
  let xf : C(W, X) := ⟨fun w => (f w).1.1, hxcont⟩
  let pf : C(W, C(I, Z)) := ⟨fun w => (f w).1.2, hpcont⟩
  -- the track condition: the path of `f w` ends at `inc (x w)`
  have hpf : ∀ w : W, pf w 1 = inc (xf w) := fun w => (f w).2
  have h0I : ((0 : I) : ℝ) = 0 := rfl
  have h1I : ((1 : I) : ℝ) = 1 := rfl
  -- ## the two branches of the lifted path
  -- branch 1: walk back along `H (·, w)` at speed `2`
  have hA : Continuous fun x : (I × W) × I =>
      H.toContinuousMap (Work.StemsB.clampI ((x.1.1 : ℝ) - 2 * (x.2 : ℝ)), x.1.2) := by
    refine H.toContinuousMap.continuous.comp (Continuous.prodMk ?_ ?_)
    · exact Work.StemsB.continuous_clampI.comp (by fun_prop)
    · exact continuous_snd.comp continuous_fst
  -- branch 2: walk along `pf w` at speed `1/(1 - s/2)`
  have hB : Continuous fun x : (I × W) × I =>
      pf x.1.2 (Work.StemsB.clampI (((x.2 : ℝ) - (x.1.1 : ℝ) / 2) / (1 - (x.1.1 : ℝ) / 2))) := by
    refine continuous_eval.comp (Continuous.prodMk ?_ ?_)
    · exact pf.continuous.comp (continuous_snd.comp continuous_fst)
    · exact Work.StemsB.continuous_clampI.comp (Continuous.div (by fun_prop) (by fun_prop)
        (fun x => by have h := x.1.1.2.2; linarith))
  -- the branches agree at the junction `t = s/2`, where both equal `H (0, w) = pf w 0`
  have hagree : ∀ x : (I × W) × I, (x.2 : ℝ) = (x.1.1 : ℝ) / 2 →
      H.toContinuousMap (Work.StemsB.clampI ((x.1.1 : ℝ) - 2 * (x.2 : ℝ)), x.1.2)
        = pf x.1.2 (Work.StemsB.clampI
            (((x.2 : ℝ) - (x.1.1 : ℝ) / 2) / (1 - (x.1.1 : ℝ) / 2))) := by
    intro x hx
    have h0 : (x.1.1 : ℝ) - 2 * (x.2 : ℝ) = 0 := by rw [hx]; ring
    have h0' : ((x.2 : ℝ) - (x.1.1 : ℝ) / 2) / (1 - (x.1.1 : ℝ) / 2) = 0 := by
      rw [hx, sub_self, zero_div]
    rw [h0, h0', Work.StemsB.clampI_zero]
    exact H.map_zero_left x.1.2
  have hΛ0 : Continuous fun x : (I × W) × I =>
      if (x.2 : ℝ) ≤ (x.1.1 : ℝ) / 2 then
        H.toContinuousMap (Work.StemsB.clampI ((x.1.1 : ℝ) - 2 * (x.2 : ℝ)), x.1.2)
      else pf x.1.2 (Work.StemsB.clampI
        (((x.2 : ℝ) - (x.1.1 : ℝ) / 2) / (1 - (x.1.1 : ℝ) / 2))) :=
    Continuous.if_le hA hB (by fun_prop) (by fun_prop) hagree
  -- ## currying: the lifted path as a continuous family
  set Λ : (I × W) × I → Z := (fun x =>
    if (x.2 : ℝ) ≤ (x.1.1 : ℝ) / 2 then
      H.toContinuousMap (Work.StemsB.clampI ((x.1.1 : ℝ) - 2 * (x.2 : ℝ)), x.1.2)
    else pf x.1.2 (Work.StemsB.clampI
      (((x.2 : ℝ) - (x.1.1 : ℝ) / 2) / (1 - (x.1.1 : ℝ) / 2)))) with hΛ_def
  have hΛ : Continuous Λ := by rw [hΛ_def]; exact hΛ0
  let Λcm : C((I × W) × I, Z) := ⟨Λ, hΛ⟩
  let cur : C(I × W, C(I, Z)) := Λcm.curry
  have hcur : ∀ (y : I × W) (t : I), cur y t = Λ (y, t) := fun y t =>
    ContinuousMap.curry_apply Λcm y t
  -- the lifted path ends at `inc (x w)`, so it defines a point of the track
  have hmem : ∀ y : I × W, cur y 1 = inc (xf y.2) := by
    intro y
    have hlt : ¬ (((1 : I) : ℝ) ≤ (y.1 : ℝ) / 2) := by
      rw [h1I]
      have h := y.1.2.2
      linarith
    have hden : (1 : ℝ) - (y.1 : ℝ) / 2 ≠ 0 := by
      have h := y.1.2.2
      linarith
    rw [hcur y 1, hΛ_def]
    dsimp only
    rw [if_neg hlt, h1I, div_self hden, Work.StemsB.clampI_one]
    exact hpf y.2
  -- ## the lifted homotopy
  have hH'cont : Continuous fun y : I × W => (⟨(xf y.2, cur y), hmem y⟩ : Track inc) :=
    Continuous.subtype_mk ((xf.continuous.comp continuous_snd).prodMk cur.continuous) hmem
  let H' : C(I × W, Track inc) := ⟨fun y => ⟨(xf y.2, cur y), hmem y⟩, hH'cont⟩
  have hcur0 : ∀ w : W, cur (0, w) = pf w := by
    intro w
    apply ContinuousMap.ext
    intro t
    by_cases ht : (t : ℝ) ≤ ((0 : I) : ℝ) / 2
    · -- `t = 0`: branch 1 gives `H (0, w) = pf w 0`
      rw [hcur (0, w) t, hΛ_def]
      dsimp only
      rw [if_pos ht]
      have ht0 : (t : ℝ) = 0 := by
        rw [h0I] at ht
        have := t.2.1
        linarith
      have harg : ((0 : I) : ℝ) - 2 * (t : ℝ) = 0 := by rw [ht0, h0I]; ring
      rw [harg, Work.StemsB.clampI_zero]
      have htI : t = 0 := Subtype.ext ht0
      rw [htI]
      have h1 : ((trackMap inc).comp f) w = pf w ((0 : I)) := rfl
      rw [← h1]
      exact H.map_zero_left w
    · -- `t > 0`: branch 2 gives `pf w (clampI t) = pf w t`
      rw [hcur (0, w) t, hΛ_def]
      dsimp only
      rw [if_neg ht]
      have harg : ((t : ℝ) - ((0 : I) : ℝ) / 2) / (1 - ((0 : I) : ℝ) / 2) = (t : ℝ) := by
        rw [h0I]; ring
      rw [harg, Work.StemsB.clampI_coe_I]
  -- the lift covers the given homotopy
  have hcover : ∀ y : I × W, trackMap inc (H' y) = H.toContinuousMap y := by
    intro y
    have hle : ((0 : I) : ℝ) ≤ (y.1 : ℝ) / 2 := by
      rw [h0I]
      have h := y.1.2.1
      linarith
    have harg : (y.1 : ℝ) - 2 * ((0 : I) : ℝ) = (y.1 : ℝ) := by rw [h0I]; ring
    show cur y 0 = H.toContinuousMap y
    rw [hcur y 0, hΛ_def]
    dsimp only
    rw [if_pos hle, harg, Work.StemsB.clampI_coe_I]
  -- ## assembly
  let g : C(W, Track inc) := ⟨fun w => H' (1, w), H'.continuous.comp
    (Continuous.prodMk (continuous_const (y := (1 : I))) continuous_id)⟩
  refine ⟨g, ?_, ?_⟩
  · refine ContinuousMap.Homotopy.mk H' ?_ ?_
    · -- the lift starts at `f`
      intro w
      exact Subtype.ext (Prod.ext rfl (hcur0 w))
    · -- the lift ends at `g`
      intro w
      rfl
  · -- the lift covers `H`
    apply ContinuousMap.ext
    rintro ⟨s, w⟩
    exact hcover (s, w)

end

/-- **The mapping-track map is a Hurewicz fibration.**  For any continuous `inc : X → Z`, the map
`trackMap inc : Track inc → Z`, `(x,γ) ↦ γ 0`, has the homotopy lifting property with respect to
every test space. -/
theorem isHurewiczFibration_trackMap {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    (inc : C(X, Z)) : Work.StemsB.IsHurewiczFibration (Work.RatHurewicz.trackMap inc) :=
  fun W _ => hasHLP_trackMap inc W

end Work.RatHurewicz
