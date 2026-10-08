import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageA.GoodRepsDef
import Submission.Work.ThmF.ChV12.prop1a

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageA.caseB_GoodReps_Phi_inj`

The map `Φ : Kset H t → G`, `k ↦ r · (k⁻¹ r⁻¹ k)` (Peterfalvi's right action `r r^{-k}`)
is injective on `Kset H t = J(D,t)`.

The proof is elementary once the two standing facts are recalled:

* `r ≠ 1`.  If `r = 1` the structure identity `t s t = r⁻¹ t r` reads `t s t = t`, hence
  `s t = 1`, i.e. `s = t⁻¹ = t ∈ H` (we have `t² = 1`), against `t ∉ H` (and `s ∈ Q ≤ H`).
* `Work.ThmF.ChV12.prop1a` (Ch. II §4 Prop. 2 (c) + `Q ⊓ D = 1`): a non-trivial
  `x ∈ Kset H t` centralises no non-trivial element of `Q`.

Given `k, k' ∈ Kset` with `r · (k⁻¹ r⁻¹ k) = r · (k'⁻¹ r⁻¹ k')`, left cancellation gives
`k⁻¹ r⁻¹ k = k'⁻¹ r⁻¹ k'`; inverting, `k⁻¹ r k = k'⁻¹ r k'`, so `a := k' k⁻¹` satisfies
`a r a⁻¹ = r`, i.e. `a` centralises `r`.  Since `Kset ⊆ Ksub = Kset` is closed under
multiplication and inverses, `a ∈ Kset`; if `a ≠ 1` then `prop1a` applied to the pair
`(a, r)` forces `r = 1`, a contradiction.  Hence `a = 1`, so `k' = k`.
-/

set_option autoImplicit false

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

theorem caseB_GoodReps_Phi_inj {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hs : s ∈ Q) (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r)
    (hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t) :
    ∀ k ∈ Work.ThmF.Kset H t, ∀ k' ∈ Work.ThmF.Kset H t,
      r * (k⁻¹ * r⁻¹ * k) = r * (k'⁻¹ * r⁻¹ * k') → k = k' := by
  intro k hk k' hk' h
  -- `t` is an involution.
  have ht2 : t * t = 1 := by
    have hpow := pow_orderOf_eq_one t
    rw [hS.split.invol, pow_two] at hpow
    exact hpow
  -- `r ≠ 1`: `r = 1` would force `s = t ∈ H`.
  have hrne : r ≠ 1 := by
    intro hr1
    have h2 : t * s * t = t := by rw [hsr, hr1]; simp
    have h5 : s * t = 1 := by
      have h6 := congrArg (fun x : G => t⁻¹ * x) h2
      simpa [mul_assoc, ht2] using h6
    have h4 : s = t⁻¹ := by
      calc s = s * t * t⁻¹ := by group
        _ = 1 * t⁻¹ := by rw [h5]
        _ = t⁻¹ := by group
    have htH : t ∈ H := by
      have htinv : t = s⁻¹ := by rw [h4]; simp
      rw [htinv]
      exact H.inv_mem (hS.split.le hs)
    exact hS.split.not_mem htH
  -- Left cancellation of `r`.
  have hcancel : k⁻¹ * r⁻¹ * k = k'⁻¹ * r⁻¹ * k' := mul_left_cancel h
  -- If `k' k⁻¹ = 1` we are done.
  by_cases ha : k' * k⁻¹ = 1
  · have hkk : k' = k := by
      have hx := congrArg (fun x : G => x * k) ha
      simpa using hx
    exact hkk.symm
  · -- Otherwise `a = k' k⁻¹` is a non-trivial element of `Kset` centralising `r ∈ Q#`.
    exfalso
    have hkKsub : k ∈ (Work.ThmF.Ksub H t : Set G) := by rw [hKsub]; exact hk
    have hk'Ksub : k' ∈ (Work.ThmF.Ksub H t : Set G) := by rw [hKsub]; exact hk'
    have hkinv : k⁻¹ ∈ Work.ThmF.Kset H t := by
      have : k⁻¹ ∈ (Work.ThmF.Ksub H t : Set G) := (Work.ThmF.Ksub H t).inv_mem hkKsub
      rwa [hKsub] at this
    have haK : k' * k⁻¹ ∈ Work.ThmF.Kset H t := by
      have h1 : k⁻¹ ∈ (Work.ThmF.Ksub H t : Set G) := by rw [hKsub]; exact hkinv
      have : k' * k⁻¹ ∈ (Work.ThmF.Ksub H t : Set G) :=
        (Work.ThmF.Ksub H t).mul_mem hk'Ksub h1
      rwa [hKsub] at this
    have hcancel' : k⁻¹ * r * k = k'⁻¹ * r * k' := by
      have := congrArg (fun x : G => x⁻¹) hcancel
      simpa [mul_inv_rev, mul_assoc] using this
    have hcomm : r * (k' * k⁻¹) = (k' * k⁻¹) * r := by
      have hconj : (k' * k⁻¹) * r * (k' * k⁻¹)⁻¹ = r := by
        have e : (k' * k⁻¹) * r * (k' * k⁻¹)⁻¹ = k' * (k⁻¹ * r * k) * k'⁻¹ := by group
        rw [e, hcancel']; group
      have h6 := congrArg (fun x : G => x * (k' * k⁻¹)) hconj
      have h7 : (k' * k⁻¹) * r = r * (k' * k⁻¹) := by simpa [mul_assoc] using h6
      exact h7.symm
    exact hrne (Work.ThmF.ChV12.prop1a hS.situation hC4 H Q t hS.split
      (k' * k⁻¹) haK ha r hr hcomm)

end Work.PSU3.StageA
