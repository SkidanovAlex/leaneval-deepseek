import Submission.Work.HilbertTowerCM.Defs
import Submission.Work.HilbertTowerCM.TotallyRealBase
import Submission.Work.HilbertTowerCM.Tower
import Submission.Work.HilbertTowerCM.Reduction
import Submission.Work.HilbertTowerCM.Main
import Submission.Work.HilbertTowerCM.Conjugation
import Submission.Work.HilbertTowerCM.Obstruction
import Submission.Work.HilbertTowerCM.closure_conjugates_eq_sup_commutators
import Submission.Work.HilbertTowerCM.closure_conjugates_eq_sup_squares
import Submission.Work.HilbertTowerCM.card_closure_conjugates_of_inversion
import Submission.Work.HilbertTowerCM.exists_isConj_of_isGalois
import Submission.Work.HilbertTowerCM.isCMField_of_isConj_of_central
import Submission.Work.HilbertTowerCM.maximalRealSubfield_eq_fixedField_conj
import Submission.Work.HilbertTowerCM.finrank_realPart_eq_card_conj
import Submission.Work.HilbertTowerCM.isCMField_iff_exists_central_isConj
import Submission.Work.HilbertTowerCM.two_lt_card_conjugates_of_inversion
import Submission.Work.HilbertTowerCM.not_isCMField_of_card_conj_gt_two
import Submission.Work.HilbertTowerCM.not_isCMField_of_inverting_involution
import Submission.Work.HilbertTowerCM.conjugationSubgroup_eq_conjugates
import Submission.Work.HilbertTowerCM.realPart_finrank_eq_index_squares
import Submission.Work.HilbertTowerCM.isCMField_iff_squares_bot_of_inverting
import Submission.Work.HilbertTowerCM.cmWall_of_benchmark

/-!
# `Submission.Work.HilbertTowerCM`: the CM endgame over `Kc = ℚ(√-30030)` in one import

This area turns the arithmetic input "the maximal unramified pro-`2` extension of `Kc` is infinite"
(`Work.ClassFieldTower.InfiniteProTwoExtension Kc`) into the CM / real-part witnesses that
`Submission.Work.CMRealSubfield` consumes, and records exactly which part of that passage is
proved and which part is the remaining arithmetic obligation.

Main entry points:

* `Work.HilbertTowerCM.UnramifiedLevel` -- a finite Galois unramified extension of a number field;
  `Work.HilbertTowerCM.exists_level_finrank_ge` -- the levels supplied by the arithmetic input;
* `Work.HilbertTowerCM.RealPartWall`, `CMLevelWall`, `HalfRealLevelWall` -- the three walls;
* **`Work.HilbertTowerCM.cmWall_iff_benchmark`** -- `CMWall` is *equivalent* to the benchmark (the
  CM-witness formulation loses nothing, and the "CM bridge" is not a structural weakening);
* `Work.HilbertTowerCM.benchmark_of_realPartWall` (constant `rootDiscr F`, no CM hypothesis),
  and `Work.HilbertTowerCM.benchmark_of_totallyReal_base` (the wall is automatic for a totally real
  base with levels unramified at the infinite places -- the route that is on the proof path),
  `cmWall_of_cmLevelWall` (constant `rootDiscr F`), `benchmark_of_halfRealLevelWall`;
* `Work.HilbertTowerCM.benchmark_of_infiniteProTwoExtension_Kc_of_realPart`,
  `cmWall_of_infiniteProTwoExtension_Kc_of_cmLevels`,
  `benchmark_of_infiniteProTwoExtension_Kc_of_cmLevels`,
  `benchmark_of_infiniteProTwoExtension_Kc_of_halfReal`;
* `Work.HilbertTowerCM.isCMField_of_central_lift`, `isCMField_of_central_lift_level`,
  `isCMField_of_isAbelianGalois_level` and the equivalence
  `Work.HilbertTowerCM.isCMField_iff_central_isConj` -- the CM criterion:
  a totally complex Galois level is CM iff its complex conjugation is central in `Gal(L/ℚ)`;
* `Work.HilbertTowerCM.maximalRealSubfield_eq_fixedField_conj`,
  `Work.HilbertTowerCM.finrank_realPart_eq_card_conj` -- the maximal real subfield is the fixed
  field of the conjugation subgroup, and `[L : L⁺]` is the order of that subgroup;
* `Work.HilbertTowerCM.not_isCMField_of_card_conj_gt_two` -- a level whose conjugation subgroup has
  order `> 2` is not CM;
* **`Work.HilbertTowerCM.not_isCMField_of_inverting_involution`** -- the end-to-end obstruction:
  a totally complex Galois level on which complex conjugation acts by inversion on a half-subgroup
  containing an element of order `> 2` is **not** CM;
* `Work.HilbertTowerCM.derivedSeries_le_squares_sup_commutators`,
  `conjugates_generate_tau_commutators`, `conjugates_generate_tau_squares`,
  `card_conjugates_of_inversion` -- the conjugation subgroup and the obstruction.

See `Submission/Work/HilbertTowerCM/README.md` for the full statement of what is proved, what the
remaining obligation is, and the numerical certificate showing that the naive
"the levels of the tower are CM" claim is false.
-/
