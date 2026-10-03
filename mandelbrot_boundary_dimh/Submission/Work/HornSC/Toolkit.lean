import Mathlib
import Submission.Lib.Unif2.Commons.Topology.Jordan.crossing_lemma_rect
import Submission.Lib.Unif2.Commons.Topology.PathConnected.isPathConnected_of_isConnected_of_open_pathConnected_nhds

/-!
# Re-export of the planar topology tools used by the `HornSC` area

This module exists so that lemmas in `Submission/Work/HornSC/` can simply
`import Submission.Work.HornSC.Toolkit` to get:

* `Commons.Topology.Jordan.crossing_lemma_rect` (Maehara's crossing lemma: in a rectangle, a
  left-right path meets a bottom-top path);
* `Commons.Topology.Jordan.crosscut_complement_not_preconnected` (a crosscut of a disc separates it);
* `Commons.Topology.Jordan.plane_separation` (Jordan curve theorem);
* `Commons.Topology.PathConnected.isPathConnected_of_isConnected_of_open_pathConnected_nhds`
  (connected + locally path connected ⟹ path connected).
-/
