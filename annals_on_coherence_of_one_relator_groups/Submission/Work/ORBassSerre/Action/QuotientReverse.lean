/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The quotient graph of a `G`-graph is a graph with involutive reversal

The reversal of arrows of the quotient graph `V/G` is involutive, so `V/G` is a graph in the
sense used throughout this development (a quiver with `Quiver.HasInvolutiveReverse`).
-/
import Submission.Work.ORBassSerre.Action.Quotient

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u v

namespace Work.ORBassSerre

open Quiver

variable {G : Type u} {V : Type v} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [GraphAction G V]

theorem orbitEReverse_involutive : Function.Involutive (orbitEReverse (G := G) (V := V)) := by
  intro E
  induction E using Quotient.inductionOn with
  | h e => simp [Quiver.Total.reverse_reverse]

instance orbitHasInvolutiveReverse : Quiver.HasInvolutiveReverse (orbitV G V) :=
  { toHasReverse := orbitHasReverse (G := G) (V := V)
    inv' := fun {A B} E => by
      apply Subtype.ext
      exact orbitEReverse_involutive E.1 }

end Work.ORBassSerre
