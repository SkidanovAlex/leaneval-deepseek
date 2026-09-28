import Mathlib
import Submission.Work.RatHurewicz.AvoidOrigin.Defs

/-!
# The transport of a point of the model along a gluing step

This module contains the computation on which the description of the class of a point of the cycle
model rests: if a point `z` of a copy of `Δ^{n+2}` is written as `facept p u` and also as the
transport of a mass distribution `x` along `τ`, then the glued partner `facept q u` is the transport
of `x` along `succAbove q ∘ invSuccAbove p ∘ τ`.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

/-- The coordinate formula for `facept`. -/
theorem facept_apply {m : ℕ} (p : Fin (m + 1)) (u : stdSimplex ℝ (Fin m)) (w : Fin (m + 1)) :
    (facept m p u : Fin (m + 1) → ℝ) w
      = ∑ v ∈ Finset.univ.filter (fun v : Fin m => Fin.succAbove p v = w), (u : Fin m → ℝ) v :=
  map_apply_eq_sum (Fin.succAbove p) u w

/-- The coordinates of a `facept` at a vertex of its image. -/
theorem facept_apply_succAbove {m : ℕ} (p : Fin (m + 1)) (u : stdSimplex ℝ (Fin m))
    (v : Fin m) : (facept m p u : Fin (m + 1) → ℝ) (Fin.succAbove p v) = (u : Fin m → ℝ) v := by
  rw [facept_apply]
  have h : Finset.univ.filter (fun v' : Fin m => Fin.succAbove p v' = Fin.succAbove p v) = {v} := by
    ext v'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => p.succAbove_right_injective h, fun h => by rw [h]⟩
  rw [h, Finset.sum_singleton]

/-- The key combinatorial identity of the gluing step: the mass at the vertex `z` lands on `w`
after the gluing exactly when `z` is the image of the preimage of `w`. -/
theorem sum_ite_succAbove {m : ℕ} [NeZero m] (p q : Fin (m + 1)) {z : Fin (m + 1)} (hz : z ≠ p)
    (w : Fin (m + 1)) (c : ℝ) :
    (∑ v : Fin m, if Fin.succAbove q v = w
        then (if z = Fin.succAbove p v then c else 0) else 0)
      = if Fin.succAbove q (invSuccAbove p z) = w then c else 0 := by
  by_cases hw : w = q
  · rw [Finset.sum_eq_zero (fun v _ => if_neg (fun h => Fin.succAbove_ne q v (h.trans hw))),
      if_neg (fun h => Fin.succAbove_ne q _ (h.trans hw))]
  · have h1 : q.succAbove (invSuccAbove q w) = w := succAbove_invSuccAbove q hw
    have hiff : (q.succAbove (invSuccAbove p z) = w) ↔ (z = p.succAbove (invSuccAbove q w)) := by
      constructor
      · intro h
        have h' : invSuccAbove p z = invSuccAbove q w :=
          q.succAbove_right_injective (h.trans h1.symm)
        calc z = p.succAbove (invSuccAbove p z) := (succAbove_invSuccAbove p hz).symm
          _ = p.succAbove (invSuccAbove q w) := by rw [h']
      · intro h
        rw [h, invSuccAbove_succAbove, h1]
    have hterm : ∀ v : Fin m,
        (if q.succAbove v = w then (if z = p.succAbove v then c else 0) else 0)
          = if v = invSuccAbove q w
              then (if z = p.succAbove (invSuccAbove q w) then c else 0) else 0 := by
      intro v
      by_cases hv : v = invSuccAbove q w
      · rw [hv, h1, if_pos rfl, if_pos rfl]
      · have h2 : q.succAbove v ≠ w := fun h =>
          hv (q.succAbove_right_injective (h.trans h1.symm))
        rw [if_neg h2, if_neg hv]
    rw [Finset.sum_congr rfl (fun v _ => hterm v)]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact if_congr hiff.symm rfl rfl

/-- **The gluing step.**  If `facept p u` is the transport of `x` along `τ`, then `facept q u` is the
transport of `x` along `succAbove q ∘ invSuccAbove p ∘ τ`. -/
theorem step_transportPt {S : Finset (Fin (n + 2))} {x : stdSimplex ℝ (Fin (n + 2))}
    (hx : ptSupport x = S) {τ : {t // t ∈ S} → Fin (n + 2)} (hτ : Function.Injective τ)
    {p q : Fin (n + 2)} (hp : ∀ t, τ t ≠ p) {u : stdSimplex ℝ (Fin (n + 1))}
    (hu : facept (n + 1) p u = transportPt x hx τ hτ)
    (hτ' : Function.Injective fun t => Fin.succAbove q (invSuccAbove p (τ t))) :
    facept (n + 1) q u = transportPt x hx (fun t => Fin.succAbove q (invSuccAbove p (τ t))) hτ' := by
  have hcoord : ∀ v : Fin (n + 1), (u : Fin (n + 1) → ℝ) v
      = ∑ t : {t // t ∈ S}, if τ t = Fin.succAbove p v then (x : Fin (n + 2) → ℝ) t else 0 := by
    intro v
    have h := congrArg (fun z : stdSimplex ℝ (Fin (n + 2)) =>
      (z : Fin (n + 2) → ℝ) (Fin.succAbove p v)) hu
    rw [facept_apply_succAbove, transportPt_apply] at h
    exact h
  refine Subtype.ext (funext fun w => ?_)
  show ((facept (n + 1) q u : stdSimplex ℝ (Fin (n + 2))) : Fin (n + 2) → ℝ) w
    = ((transportPt x hx (fun t => Fin.succAbove q (invSuccAbove p (τ t))) hτ' :
        stdSimplex ℝ (Fin (n + 2))) : Fin (n + 2) → ℝ) w
  have hcalc : ((facept (n + 1) q u : Fin (n + 2) → ℝ) w)
      = ∑ v : Fin (n + 1), ∑ t : {t // t ∈ S},
          if Fin.succAbove q v = w
            then (if τ t = Fin.succAbove p v then (x : Fin (n + 2) → ℝ) t else 0)
            else 0 := by
    rw [facept_apply, Finset.sum_filter]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hcoord v]
    by_cases h : Fin.succAbove q v = w
    · simp only [h, if_true]
    · simp only [h, if_false, Finset.sum_const_zero]
  rw [hcalc, Finset.sum_comm, transportPt_apply]
  exact Finset.sum_congr rfl fun t _ => sum_ite_succAbove p q (hp t) w _

end

end Work.RatHurewicz
