/-
Copyright: subproject `Submission/Work/Implosion/` of `mandelbar_not_path_connected`.

# `Submission.Work.Implosion` — the local parabolic implosion of Hubbard–Schleicher §4

Aggregator: import this module to get the whole chapter — the normal form, the Écalle
coordinate, the displacement/eggbeater estimates, the transit-phase blow-up `π/‖a‖`, the
fundamental domains, the Écalle cylinder with its explicit chord chart, and the
**approximate perturbed Fatou coordinate** `approxEcal` with its step and transit
estimates (the current deliverable, per `NOTES_LEAD_mandelbar_flower.md` §B).

See `Submission/Work/Implosion/NOTES.md` for conventions, the main theorem names, and the
items deliberately left out.
-/
import Submission.Work.Implosion.Basic
import Submission.Work.Implosion.Ecalle
import Submission.Work.Implosion.Disp
import Submission.Work.Implosion.Phase
import Submission.Work.Implosion.Geometry
import Submission.Work.Implosion.Cylinder
import Submission.Work.Implosion.Chord
import Submission.Work.Implosion.Approx

-- delegated lemmas
import Submission.Work.Implosion.Ecalle.ecallePt_hasDerivAt
import Submission.Work.Implosion.Ecalle.ecallePt_eq_coth
import Submission.Work.Implosion.Ecalle.ecallePt_injective_mod_lattice
import Submission.Work.Implosion.Ecalle.ecalCoord_ecalPt
import Submission.Work.Implosion.Ecalle.ecalleHeight_eq_zero
import Submission.Work.Implosion.Ecalle.ecalCoord_cutPt_im
import Submission.Work.Implosion.Ecalle.ecallePt_tendsto_fixed
import Submission.Work.Implosion.Ecalle.mobius_injective_of_ne
import Submission.Work.Implosion.Disp.ecalPt_add_modelDisp
import Submission.Work.Implosion.Geometry.normalForm_cutPt_re
import Submission.Work.Implosion.Geometry.imageCut_disjoint_cut
import Submission.Work.Implosion.Cylinder.exp_two_pi_I_strip_rep
import Submission.Work.Implosion.Cylinder.existsUnique_slab_rep
import Submission.Work.Implosion.Cylinder.exists_im_ne_zero_near_zero
import Submission.Work.Implosion.Cylinder.mem_periodZMod_iff
import Submission.Work.Implosion.Cylinder.ecalPt_eq_of_mem_periodZMod
import Submission.Work.Implosion.Cylinder.periodZMod_equiv_model
import Submission.Work.Implosion.Phase.modelOrbit_re_decrease
import Submission.Work.Implosion.Phase.modelOrbit_slab_at_most_once
import Submission.Work.Implosion.Chord.chordPt_re_im
import Submission.Work.Implosion.Chord.chordPt_injective
import Submission.Work.Implosion.Chord.chordHeight_bij
import Submission.Work.Implosion.Chord.chordHeight_eq_ecalleHeight
import Submission.Work.Implosion.Chord.chordCylCoord_fibres_range
import Submission.Work.Implosion.Chord.cylindrical_fundamentalDomain
import Submission.Work.Implosion.Chord.exists_conj_translation
import Submission.Work.Implosion.Chord.levelMap_strictMono
import Submission.Work.Implosion.Approx.modelDisp_second_order
import Submission.Work.Implosion.Approx.hasDerivAt_log_sinh_div
import Submission.Work.Implosion.Approx.approxEcal_end_out
import Submission.Work.Implosion.Approx.approxEcal_step
import Submission.Work.Implosion.Approx.approxEcal_transit
import Submission.Work.Implosion.Approx.approxEcal_shift
import Submission.Work.Implosion.Approx.approxEcal_reflect
import Submission.Work.Implosion.Approx.ecalCoord_conj
import Submission.Work.Implosion.Approx.ecalCoord_reflect
import Submission.Work.Implosion.Approx.approxEcal_end_in
import Submission.Work.Implosion.Approx.sum_inv_sq_le_of_mono
import Submission.Work.Implosion.Approx.sum_inv_sq_le_of_step

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion

end Work.Implosion
