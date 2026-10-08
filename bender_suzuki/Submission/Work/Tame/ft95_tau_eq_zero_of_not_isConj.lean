import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.Tau
import Submission.Work.Tame.tau_eq_zero_of_not_isConj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Feit–Thompson Lemma 9.1 (vanishing part), re-exported

This module exists for the historical reason that the proof of Lemma 9.5
(`Submission/Work/Tame/ft9_5.lean`) imports it; it is now just a re-export of
`Work.Tame.tau_eq_zero_of_not_isConj`.
-/

namespace Work.Tame

open Classical

/-- **Feit–Thompson Lemma 9.1, vanishing part** (p. 805): `α^τ(x) = 0` for `x` conjugate to no
element of any `𝔄_L`.  Re-export of `Work.Tame.tau_eq_zero_of_not_isConj`. -/
theorem ft95_tau_eq_zero_of_not_isConj {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} (h : IsTamelyImbedded Lhat n Hs) (hD : HasTameData Lhat n Hs)
    {α : ↥(Lgrp Lhat) → ℂ} (hα : α ∈ C0 Lhat) {x : X} (hx : ¬ inConjAU Lhat n Hs x) :
    tau Lhat n Hs α x = 0 :=
  tau_eq_zero_of_not_isConj h hD hα hx

end Work.Tame
