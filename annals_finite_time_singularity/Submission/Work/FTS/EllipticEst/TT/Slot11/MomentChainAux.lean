/-
Copyright: work module for the Elgindi finite-time singularity project.

# `TT.Slot11.MomentChainAux`: the angular-moment chain, re-exported

This module used to carry a *self-contained copy* of the angular-moment chain
`F_*(D_z^j \u03a8) \u2261 0` (`j \u2264 3`) for the `a.e.` weak class `TT.EllWeakPos`, in the namespace
`Work.H2W.MomentAe` (the copy was made when the module
`Submission/Work/H2W/momentChainAe.lean` was temporarily unavailable).

That duplicate clashed with the identical development in
`Submission/Work/H2W/momentChainAe.lean` -- same namespace, same declaration names -- as soon as
a single file imported both, so the content is now taken from there.  The present module is
kept because several files import it for those names (and because it also re-exports the
`Work.FTS.EllipticEst.TTSlot11Aux` lemmas of `ZsqAux`), but it declares nothing new.
-/
import Mathlib.Tactic.MinImports
import Submission.Work.H2W.momentChainAe
import Submission.Work.FTS.EllipticEst.TT.Slot11.ZsqAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
