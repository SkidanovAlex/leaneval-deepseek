import Submission.ComponentChart
import Submission.Work.Drive.strip_defs

/-!
# Re-export wrapper: trisecant-set vocabulary

Thin re-export module so that sibling developments under `Submission/Work/` can name

* `LeanEval.KnotTheory.Quadrisecant.OSub r` (the secant classes in Kuperberg's set `O`),
  `ChartInterval`, `chartTrace`, `osub_local_interval`, `component_local_interval`
  (the local interval charts of `O`) — from `Submission/ComponentChart.lean`;
* `LeanEval.KnotTheory.Quadrisecant.trisecantSet`,
  `exists_open_pathConnected_nhds_in_O`, `isOpen_component_in_O`,
  `component_isPathConnected_in_O` — the same file's neighbourhood vocabulary.

`Submission.ComponentChart` is not under `Submission/Work/`, so it cannot be named in a
`depends_on` list; this file puts the vocabulary one hop closer. It contains no declarations
of its own.
-/
