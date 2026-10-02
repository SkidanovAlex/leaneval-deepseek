import Mathlib
import Submission.Work.StemsB.Fibrations

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The path–loop fibration `PX → X` is a Serre fibration

For a based space `(X, x₀)` the *path space* `PathSpace X x₀` (`Submission/Work/StemsB/Fibrations.lean`)
is the space of paths in `X` starting at `x₀`, and `evalOne X x₀ : PathSpace X x₀ → X` sends a path
to its endpoint.  Its fibre over `x₀` is the loop space `Ω X = Path x₀ x₀`, so `evalOne` is the
*path–loop fibration*, the source of every long exact sequence of homotopy groups
(`Work.StemsB.homotopyGroup_loopSpace`).

This file proves that `evalOne` has the homotopy lifting property with respect to *every* space `Z`,
i.e. that `evalOne` is a Hurewicz fibration — in particular (`hasHLP_evalOne`) a Serre fibration
(`isSerreFibration_evalOne`).

## The lift

Given `f : Z → PathSpace X x₀` and a homotopy `H : I × Z → X` of `evalOne ∘ f`, the lifted homotopy
is the family of concatenations

`Ψ (t, z, s) = if s ≤ 1 - t/2 then (f z) (s / (1 - t/2)) else H (2s - 2 + t, z)`

— the path `f z` reparametrised onto `[0, 1 - t/2]`, followed by the path traced by `H`.  At `t = 0`
this is exactly `f z`; at `t = 1` it ends at `H (1, z)`; and at `s = 0` it starts at `x₀`.  The
junction is at `s = 1 - t/2`, where both branches take the value `(f z) 1 = H (0, z)`, which is what
makes the piecewise definition continuous (`Continuous.if_le`); the two branches themselves are
global continuous functions thanks to the clamping map `clampI : ℝ → I`.

## Main declarations

* `Work.StemsB.clampI`, `Work.StemsB.clampI_coe_I` — the clamping of `ℝ` onto `I = [0,1]`.
* `Work.StemsB.hasHLP_evalOne` — `evalOne` has the HLP with respect to every space.
* `Work.StemsB.isSerreFibration_evalOne` — `evalOne` is a Serre fibration.
-/

open scoped Topology unitInterval

namespace Work.StemsB

noncomputable section

/-! ## Clamping `ℝ` to the unit interval -/

/-- The clamping map `ℝ → I = [0,1]`, given by `Set.projIcc`.  It is continuous and it is the
identity on `I`; it is used to make the two branches of the lifted homotopy *everywhere defined*
continuous functions, so that the piecewise gluing lemma `Continuous.if_le` applies. -/
def clampI : ℝ → I := Set.projIcc 0 1 zero_le_one

theorem continuous_clampI : Continuous clampI := continuous_projIcc

theorem clampI_of_mem {r : ℝ} (hr : r ∈ Set.Icc (0:ℝ) 1) : clampI r = ⟨r, hr⟩ :=
  Set.projIcc_of_mem zero_le_one hr

theorem clampI_zero : clampI 0 = (0 : I) := by
  rw [clampI_of_mem (by norm_num : (0:ℝ) ∈ Set.Icc 0 1)]; rfl

theorem clampI_one : clampI 1 = (1 : I) := by
  rw [clampI_of_mem (by norm_num : (1:ℝ) ∈ Set.Icc 0 1)]; rfl

/-- `clampI` fixes the unit interval. -/
theorem clampI_coe_I (s : I) : clampI (s:ℝ) = s := by
  rw [clampI_of_mem s.2]

/-! ## The homotopy lifting property of `evalOne` -/

/-- The endpoint evaluation `evalOne X x₀ : PathSpace X x₀ → X` has the homotopy lifting property
with respect to **every** topological space `Z`: the path space fibration is a Hurewicz
fibration. -/
theorem hasHLP_evalOne (X : Type*) [TopologicalSpace X] (x₀ : X) (Z : Type*)
    [TopologicalSpace Z] : HasHLP (evalOne X x₀) Z := by
  classical
  intro f b H
  -- the uncurried form of `f` (a continuous function `Z × I → X`)
  have hF : Continuous fun p : Z × I => (f p.1).1 p.2 :=
    continuous_eval.comp
      (((continuous_subtype_val.comp f.continuous).comp continuous_fst).prodMk continuous_snd)
  -- branch 1: walk along `f z` at speed `1/(1 - t/2) ∈ [1,2]`
  let A : (I × Z) × I → X := fun x =>
    (f x.1.2).1 (clampI ((x.2 : ℝ) / (1 - (x.1.1 : ℝ) / 2)))
  -- branch 2: walk along the path traced by `H` at speed `2`
  let B : (I × Z) × I → X := fun x =>
    H (clampI (2 * (x.2 : ℝ) - 2 + (x.1.1 : ℝ)), x.1.2)
  have hA : Continuous A := by
    show Continuous fun x : (I × Z) × I =>
      (f x.1.2).1 (clampI ((x.2 : ℝ) / (1 - (x.1.1 : ℝ) / 2)))
    refine hF.comp (Continuous.prodMk (continuous_snd.comp continuous_fst) ?_)
    exact continuous_clampI.comp (Continuous.div (by fun_prop) (by fun_prop) (fun x => by
      have h := x.1.1.2.2; linarith))
  have hB : Continuous B := by
    show Continuous fun x : (I × Z) × I =>
      H (clampI (2 * (x.2 : ℝ) - 2 + (x.1.1 : ℝ)), x.1.2)
    exact H.toContinuousMap.continuous.comp (Continuous.prodMk
      (continuous_clampI.comp (by fun_prop)) (continuous_snd.comp continuous_fst))
  -- the two branches agree at the junction `s = 1 - t/2`, where both equal `(f z) 1 = H (0, z)`
  have hAgree : ∀ x : (I × Z) × I, (x.2 : ℝ) = 1 - (x.1.1 : ℝ) / 2 → A x = B x := by
    intro x hx
    have hne : (1 : ℝ) - (x.1.1 : ℝ) / 2 ≠ 0 := by have h := x.1.1.2.2; linarith
    have h1 : (x.2 : ℝ) / (1 - (x.1.1 : ℝ) / 2) = 1 := by rw [hx, div_self hne]
    have h2 : 2 * (x.2 : ℝ) - 2 + (x.1.1 : ℝ) = 0 := by rw [hx]; ring
    show (f x.1.2).1 (clampI _) = H (clampI _, x.1.2)
    rw [h1, h2, clampI_one, clampI_zero]
    exact (H.apply_zero x.1.2).symm
  have hΨ0 : Continuous fun x : (I × Z) × I =>
      if (x.2 : ℝ) ≤ 1 - (x.1.1 : ℝ) / 2 then A x else B x :=
    Continuous.if_le hA hB (by fun_prop) (by fun_prop) hAgree
  set Ψ : (I × Z) × I → X :=
    (fun x => if (x.2 : ℝ) ≤ 1 - (x.1.1 : ℝ) / 2 then A x else B x) with hΨ_def
  have hΨ : Continuous Ψ := by rw [hΨ_def]; exact hΨ0
  -- `Ψ` is continuous, hence its currying is a continuous map into the path space
  let Ψcm : C((I × Z) × I, X) := ⟨Ψ, hΨ⟩
  let cur : C(I × Z, C(I, X)) := Ψcm.curry
  have hcur : ∀ (y : I × Z) (s : I), cur y s = Ψ (y, s) := fun y s =>
    ContinuousMap.curry_apply Ψcm y s
  -- each `cur y` is a path starting at `x₀`
  have hbase : ∀ y : I × Z, cur y 0 = x₀ := by
    rintro ⟨t, z⟩
    have hcon : ((0 : I) : ℝ) ≤ 1 - (t : ℝ) / 2 := by
      have h : ((0 : I) : ℝ) = 0 := rfl
      rw [h]; have := t.2.2; linarith
    rw [hcur (t, z) 0, hΨ_def]
    dsimp only
    rw [if_pos hcon]
    show (f z).1 (clampI (((0 : I) : ℝ) / (1 - (t : ℝ) / 2))) = x₀
    have h0 : ((0 : I) : ℝ) = 0 := rfl
    rw [h0, zero_div, clampI_zero]
    exact (f z).2
  let H'cm : C(I × Z, PathSpace X x₀) :=
    ⟨fun y => ⟨cur y, hbase y⟩, Continuous.subtype_mk cur.continuous hbase⟩
  let g : C(Z, PathSpace X x₀) :=
    ⟨fun z => H'cm (1, z), H'cm.continuous.comp (Continuous.prodMk
      (continuous_const (y := (1 : I))) continuous_id)⟩
  refine ⟨g, ?_, ?_⟩
  · refine ContinuousMap.Homotopy.mk H'cm ?_ ?_
    · -- at time `0` the lift is `f` itself
      intro z
      apply Subtype.ext
      apply ContinuousMap.ext
      intro s
      show cur (0, z) s = (f z).1 s
      have hcon : (s : ℝ) ≤ 1 - ((0 : I) : ℝ) / 2 := by
        have h : ((0 : I) : ℝ) = 0 := rfl
        rw [h]; have := s.2.2; linarith
      rw [hcur (0, z) s, hΨ_def]
      dsimp only
      rw [if_pos hcon]
      show (f z).1 (clampI ((s : ℝ) / (1 - ((0 : I) : ℝ) / 2))) = (f z).1 s
      have h0 : ((0 : I) : ℝ) = 0 := rfl
      rw [h0, zero_div, sub_zero, div_one, clampI_coe_I]
    · -- at time `1` the lift is the pointwise endpoint
      intro z
      rfl
  · -- the lift covers `H`
    apply ContinuousMap.ext
    rintro ⟨t, z⟩
    show cur (t, z) 1 = H (t, z)
    have h1I : ((1 : I) : ℝ) = 1 := rfl
    by_cases h : ((1 : I) : ℝ) ≤ 1 - (t : ℝ) / 2
    · -- `t = 0`, and then the endpoint is `(f z) 1 = H (0, z)`
      rw [hcur (t, z) 1, hΨ_def]
      dsimp only
      rw [if_pos h]
      show (f z).1 (clampI (((1 : I) : ℝ) / (1 - (t : ℝ) / 2))) = H (t, z)
      have ht : (t : ℝ) = 0 := by have := t.2.1; linarith
      have hte : t = 0 := Subtype.ext ht
      rw [hte]
      have h0 : ((0 : I) : ℝ) = 0 := rfl
      rw [h1I, h0, zero_div, sub_zero, div_one, clampI_one]
      exact (H.apply_zero z).symm
    · -- `t > 0`, and then the endpoint is `H (t, z)`
      rw [hcur (t, z) 1, hΨ_def]
      dsimp only
      rw [if_neg h]
      show H (clampI (2 * ((1 : I) : ℝ) - 2 + (t : ℝ)), z) = H (t, z)
      have key : 2 * ((1 : I) : ℝ) - 2 + (t : ℝ) = (t : ℝ) := by
        rw [h1I]; ring
      rw [key, clampI_coe_I]

/-- **The path–loop fibration**: the endpoint evaluation `PathSpace X x₀ → X` is a Serre fibration.
Its fibre over `x₀` is the loop space `Ω X`. -/
theorem isSerreFibration_evalOne (X : Type*) [TopologicalSpace X] (x₀ : X) :
    Work.StemsB.IsSerreFibration (Work.StemsB.evalOne X x₀) :=
  fun n => hasHLP_evalOne X x₀ (Fin n → I)

end

end Work.StemsB
