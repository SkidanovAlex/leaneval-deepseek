import Mathlib
import Submission.Work.Bottcher.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Lift changes of nowhere-zero paths through the exponential covering

Elementary covering-theory vocabulary for
`Work.Bottcher.Contraction.exists_analytic_log_normFactor_of_mem_mandelbar`.

For a nowhere-zero path `δ : C(I, ℂ)` we define its **lift change** `liftChange δ hδ`: the
difference between the value at `1` and the value at `0` of the (unique) continuous lift of `δ`
through `Complex.exp` that starts at `Complex.log (δ 0)`.  It measures the winding of `δ` around
`0`; the exponential of the lift change is `δ 1 / δ 0`.
-/

open Filter Function
open scoped Topology

namespace Work.Bottcher.Contraction

noncomputable section

/-- The continuous map `t ↦ ⟨δ t, _⟩ : C(I, ℂ*)` induced by a nowhere-zero path. -/
def pathSubtype (δ : C(unitInterval, ℂ)) (hδ : ∀ t, δ t ≠ 0) : C(unitInterval, {z : ℂ // z ≠ 0}) :=
  ⟨fun t => ⟨δ t, hδ t⟩, δ.continuous.subtype_mk hδ⟩

@[simp] theorem pathSubtype_apply (δ : C(unitInterval, ℂ)) (hδ : ∀ t, δ t ≠ 0) (t : unitInterval) :
    ((pathSubtype δ hδ t : {z : ℂ // z ≠ 0}) : ℂ) = δ t := rfl

/-- The translate `t ↦ γ t - p` of a path. -/
def pathSub (γ : C(unitInterval, ℂ)) (p : ℂ) : C(unitInterval, ℂ) :=
  γ - ContinuousMap.const unitInterval p

@[simp] theorem pathSub_apply (γ : C(unitInterval, ℂ)) (p : ℂ) (t : unitInterval) :
    pathSub γ p t = γ t - p := rfl

theorem pathSub_ne_zero {γ : C(unitInterval, ℂ)} {p : ℂ} (h : ∀ t, γ t ≠ p) :
    ∀ t, pathSub γ p t ≠ 0 := fun t => sub_ne_zero.mpr (h t)

/-- A lift of a nowhere-zero path through the exponential covering, with prescribed value at `0`. -/
def liftOf (δ : C(unitInterval, ℂ)) (hδ : ∀ t, δ t ≠ 0) (e : ℂ) (he : Complex.exp e = δ 0) :
    C(unitInterval, ℂ) :=
  Complex.isCoveringMap_exp.liftPath (pathSubtype δ hδ) e (Subtype.ext he.symm)

theorem liftOf_apply_zero (δ : C(unitInterval, ℂ)) (hδ : ∀ t, δ t ≠ 0) (e : ℂ)
    (he : Complex.exp e = δ 0) : liftOf δ hδ e he 0 = e := by
  have h := Complex.isCoveringMap_exp.liftPath_zero (γ := pathSubtype δ hδ) (e := e)
    (γ_0 := Subtype.ext he.symm)
  simpa [liftOf] using h

theorem exp_liftOf (δ : C(unitInterval, ℂ)) (hδ : ∀ t, δ t ≠ 0) (e : ℂ)
    (he : Complex.exp e = δ 0) (t : unitInterval) : Complex.exp (liftOf δ hδ e he t) = δ t := by
  have h := Complex.isCoveringMap_exp.liftPath_lifts (γ := pathSubtype δ hδ) (e := e)
    (γ_0 := Subtype.ext he.symm)
  have h2 : (fun s => (⟨Complex.exp (liftOf δ hδ e he s), Complex.exp_ne_zero _⟩ :
      {z : ℂ // z ≠ 0})) = pathSubtype δ hδ := h
  exact Subtype.ext_iff.mp (congrFun h2 t)

/-- **Lift change** of a nowhere-zero path: the difference between the endpoint and the starting
point of the lift through `Complex.exp` that starts at `Complex.log (δ 0)`. -/
def liftChange (δ : C(unitInterval, ℂ)) (hδ : ∀ t, δ t ≠ 0) : ℂ :=
  liftOf δ hδ (Complex.log (δ 0)) (Complex.exp_log (hδ 0)) 1 - Complex.log (δ 0)

/-- The exponential of the lift change is the ratio of the endpoint to the starting point. -/
theorem exp_liftChange (δ : C(unitInterval, ℂ)) (hδ : ∀ t, δ t ≠ 0) :
    Complex.exp (liftChange δ hδ) = δ 1 / δ 0 := by
  have h1 : Complex.exp (liftOf δ hδ (Complex.log (δ 0)) (Complex.exp_log (hδ 0)) 1) = δ 1 :=
    exp_liftOf δ hδ _ _ 1
  rw [liftChange, Complex.exp_sub, h1, Complex.exp_log (hδ 0)]

/-- Shifting the starting lift shifts the whole lift by a constant. -/
theorem liftOf_shift (δ : C(unitInterval, ℂ)) (hδ : ∀ t, δ t ≠ 0) (e e' : ℂ)
    (he : Complex.exp e = δ 0) (he' : Complex.exp e' = δ 0) :
    liftOf δ hδ e' he' = fun t => liftOf δ hδ e he t + (e' - e) := by
  have hc : Continuous fun t : unitInterval => liftOf δ hδ e he t + (e' - e) :=
    (liftOf δ hδ e he).continuous.add_const _
  have hcomp : (fun z => (⟨Complex.exp z, Complex.exp_ne_zero _⟩ : {z : ℂ // z ≠ 0}))
      ∘ (fun t => liftOf δ hδ e he t + (e' - e)) = pathSubtype δ hδ := by
    funext t
    show (⟨Complex.exp (liftOf δ hδ e he t + (e' - e)), _⟩ : {z : ℂ // z ≠ 0}) = _
    rw [Subtype.ext_iff]
    show Complex.exp (liftOf δ hδ e he t + (e' - e)) = δ t
    rw [Complex.exp_add, exp_liftOf δ hδ e he t]
    have h2 : Complex.exp (e' - e) = δ 0 / Complex.exp e := by
      rw [Complex.exp_sub, he']
    rw [h2, he]
    rw [div_self (hδ 0), mul_one]
  have h0 : (fun t => liftOf δ hδ e he t + (e' - e)) 0 = e' := by
    show liftOf δ hδ e he 0 + (e' - e) = e'
    rw [liftOf_apply_zero]
    ring
  have h := (Complex.isCoveringMap_exp.eq_liftPath_iff (γ := pathSubtype δ hδ) (e := e')
    (γ_0 := Subtype.ext he'.symm)).mpr ⟨hc, hcomp, h0⟩
  simpa [liftOf] using h.symm

/-- **The lift change does not depend on the chosen starting lift.** -/
theorem liftChange_eq_liftOf (δ : C(unitInterval, ℂ)) (hδ : ∀ t, δ t ≠ 0) (e : ℂ)
    (he : Complex.exp e = δ 0) : liftChange δ hδ = liftOf δ hδ e he 1 - e := by
  have h := congrFun (liftOf_shift δ hδ e (Complex.log (δ 0)) he (Complex.exp_log (hδ 0))) 1
  rw [liftChange]
  rw [h]
  ring

/-- The lift change of a nowhere-zero closed path lies in `2πiℤ`. -/
theorem liftChange_mem_zmultiples (δ : C(unitInterval, ℂ)) (hδ : ∀ t, δ t ≠ 0)
    (hloop : δ 1 = δ 0) :
    ∃ n : ℤ, liftChange δ hδ = n * (2 * Real.pi * Complex.I) := by
  have h : Complex.exp (liftChange δ hδ) = 1 := by
    rw [exp_liftChange, hloop, div_self (hδ 0)]
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  exact ⟨n, hn⟩

end

end Work.Bottcher.Contraction
