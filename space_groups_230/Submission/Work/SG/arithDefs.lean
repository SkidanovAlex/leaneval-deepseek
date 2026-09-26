import Mathlib
import Submission.Work.SG.Defs

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-!
# Shared definitions and data for `arithRep_conj_eq`

This module holds the generated data and the definitions/lemmas shared with the two lemmas
proved in `Submission.Work.SG.trPow_card_conj` and `Submission.Work.SG.fixPow_conj`:

* the explicit element lists `ELcodes` of the 73 arithmetic-class representatives, with kernel
  certificates certifying that they are exactly `arithRep j` (`mem_arithRep`);
* the conjugation invariant `invOf` (cardinality, trace power sums, and power sums of the numbers
  of fixed vectors of the actions on `(ℤ/2)³`, `(ℤ/3)³`, `(ℤ/4)³`), together with the kernel check
  that it separates the 73 representatives (`invOf_nodup`).

The main theorem is in `Submission.Work.SG.arithRep_conj_eq`.
-/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem
open scoped BigOperators

/-! ## Generated data -/

def ELcodes : List (List ℕ) := [
  [16484],
  [16484, 3198],
  [16484, 16372],
  [16484, 3362],
  [16484, 3250],
  [16484, 16320],
  [16484, 10324, 7636],
  [16484, 16377, 16345],
  [16484, 3198, 3250, 16432],
  [16484, 3198, 16320, 3362],
  [16484, 3304, 16320, 3256],
  [16484, 7606, 11514, 3760],
  [16484, 11514, 16624, 11374],
  [16484, 3250, 16372, 3362],
  [16484, 16320, 16482, 16322],
  [16484, 16320, 16372, 16432],
  [16484, 11514, 15726, 12272],
  [16484, 16320, 3250, 3310],
  [16484, 16320, 3360, 3200],
  [16484, 11514, 8308, 3058],
  [16484, 11514, 7410, 3956],
  [16484, 15922, 11514, 12076],
  [16484, 16426, 16320, 16378],
  [16484, 8866, 12064, 3198, 10816, 7618],
  [16484, 3337, 16377, 3198, 16345, 3305],
  [16484, 3255, 16345, 3362, 16377, 3223],
  [16484, 10324, 16372, 7636, 7412, 10660],
  [16484, 16377, 16485, 16345, 16349, 16372],
  [16484, 16377, 16455, 16345, 16432, 16319],
  [16484, 12064, 7410, 10816, 3250, 9022],
  [16484, 16377, 3363, 16345, 3227, 3250],
  [16484, 16377, 3333, 16345, 3310, 3197],
  [16484, 16459, 16377, 16320, 16345, 16427],
  [16484, 15922, 7606, 11514, 3198, 12076, 3760, 8168],
  [16484, 3304, 16426, 16320, 3198, 3256, 16378, 3362],
  [16484, 3198, 16320, 3250, 3362, 16432, 3310, 16372],
  [16484, 11514, 15726, 3198, 12272, 8168, 3956, 7410],
  [16484, 3198, 16320, 3360, 3362, 16322, 3200, 16482],
  [16484, 11514, 3198, 16624, 8168, 11374, 3058, 8308],
  [16484, 3304, 16482, 16320, 3250, 3310, 3256, 16322],
  [16484, 11526, 11514, 7410, 16494, 7400, 3944, 3956],
  [16484, 7606, 15726, 11514, 8308, 3058, 3760, 12272],
  [16484, 11784, 16320, 3200, 7412, 12272, 7896, 3360],
  [16484, 15922, 15726, 11514, 16624, 11374, 12076, 12272],
  [16484, 16426, 16482, 16320, 16372, 16432, 16378, 16322],
  [16484, 11786, 16320, 3200, 7410, 12270, 7898, 3360],
  [16484, 15738, 11514, 7410, 12282, 3188, 8156, 3956],
  [16484, 3255, 3337, 16345, 16320, 16377, 3362, 3305, 3223, 3198, 16459, 16427],
  [16484, 8866, 7410, 12064, 10660, 16432, 3198, 3250, 9022, 7618, 10816, 12272],
  [16484, 3337, 16455, 16377, 3363, 3250, 3198, 16432, 16319, 3305, 16345, 3227],
  [16484, 3337, 3333, 16377, 16485, 16372, 3198, 3310, 3197, 3305, 16345, 16349],
  [16484, 3255, 3333, 16345, 16432, 16319, 3362, 3197, 3310, 3223, 16377, 16455],
  [16484, 3255, 3363, 16345, 16349, 16372, 3362, 3250, 3227, 3223, 16377, 16485],
  [16484, 16459, 16455, 16377, 16485, 16372, 16320, 16432, 16319, 16427, 16345, 16349],
  [16484, 16459, 3333, 16377, 3363, 3250, 16320, 3310, 3197, 16427, 16345, 3227],
  [16484, 10324, 9352, 7636, 7672, 12064, 11992, 3360, 16320, 3200, 8872, 10816],
  [16484, 9174, 15648, 3838, 8308, 3058, 14158, 5216, 12064, 10816, 7814, 11514],
  [16484, 16620, 8925, 16597, 9022, 8308, 8158, 9334, 8573, 5252, 5269, 5550],
  [16484, 11526, 15738, 11514, 7410, 3198, 16494, 12282, 7400, 3188, 3944, 8156, 3956, 8168, 15726, 12272],
  [16484, 11784, 11786, 16320, 3200, 3198, 7412, 7410, 12272, 12270, 7896, 7898, 3360, 3362, 16322, 16482],
  [16484, 3255, 3337, 3333, 16345, 16320, 16432, 16377, 16485, 16319, 16372, 3362, 3305, 3197, 3223, 3227, 3363, 3198, 3310, 3250, 16459, 16455, 16349, 16427],
  [16484, 14430, 11524, 8573, 5269, 16597, 8925, 3198, 10660, 11374, 14132, 5252, 8158, 9334, 16620, 11109, 14413, 3085, 10757, 9022, 8308, 5550, 10348, 3062],
  [16484, 8866, 10810, 12064, 11992, 7636, 7672, 3198, 16322, 3362, 16482, 10816, 8872, 9352, 10324, 7618, 7690, 12046, 12010, 3360, 16320, 3200, 10330, 9358],
  [16484, 14466, 8866, 7814, 15648, 3838, 12064, 3198, 16624, 8168, 11374, 5216, 10816, 14158, 9174, 11868, 4034, 15844, 7618, 3058, 11514, 8308, 5524, 10508],
  [16484, 11784, 3304, 3200, 10816, 7636, 16320, 7896, 16372, 9184, 7412, 16432, 12272, 3256, 8872, 12064, 3360, 10324, 9352, 11992, 7672, 10480, 9040, 10660],
  [16484, 11280, 9330, 3058, 14158, 3838, 8308, 8542, 10660, 12272, 3110, 14132, 16432, 5242, 5216, 15648, 11514, 9174, 10816, 12064, 7814, 7606, 3760, 15726],
  [16484, 9330, 5280, 8308, 8158, 16597, 9022, 5242, 16592, 5549, 16624, 8914, 8168, 8578, 9334, 8925, 5550, 16620, 5252, 8573, 5269, 8293, 9037, 16485],
  [16484, 16426, 10642, 16320, 10324, 7672, 3360, 16378, 10498, 7410, 3250, 9022, 3310, 9202, 10816, 7636, 3200, 8872, 9352, 11992, 12064, 7898, 11786, 12270],
  [16484, 15922, 14440, 11514, 7814, 9174, 8308, 12076, 9022, 3250, 3956, 5550, 7410, 10352, 15648, 5216, 3058, 3838, 12064, 10816, 14158, 11140, 8402, 16572],
  [16484, 14440, 11389, 8308, 8925, 9334, 5550, 10352, 14133, 3090, 3058, 3197, 11514, 10645, 16597, 8158, 9022, 5269, 8573, 5252, 16620, 14402, 11104, 10768],
  [16484, 8866, 10810, 11784, 12064, 11992, 10498, 7636, 7672, 9202, 3310, 16378, 3200, 3198, 16322, 3256, 3362, 16482, 3304, 7896, 7412, 9358, 16432, 16372, 12272, 10330, 10480, 9040, 7618, 9184, 10660, 12046, 10816, 8872, 7898, 9352, 10324, 12270, 10642, 7410, 11786, 9022, 16426, 3250, 16320, 3360, 7690, 12010],
  [16484, 14466, 8866, 11280, 7814, 15648, 12076, 3838, 12064, 3956, 10352, 5550, 3058, 3198, 16624, 10660, 8168, 11374, 5242, 16432, 3110, 14132, 9330, 8542, 15726, 7606, 15844, 12272, 3760, 7618, 5524, 10508, 5216, 10816, 8402, 14158, 9174, 11140, 15922, 7410, 16572, 3250, 14440, 9022, 11514, 8308, 11868, 4034],
  [16484, 14430, 11524, 9330, 8573, 5269, 3197, 16597, 8925, 14133, 10768, 3090, 8308, 3198, 10660, 5280, 11374, 14132, 16592, 5242, 8168, 10348, 8914, 8578, 3062, 9037, 16485, 11109, 5549, 8293, 10757, 5252, 8158, 10352, 9334, 16620, 11514, 11389, 14440, 3058, 11104, 14402, 5550, 10645, 9022, 14413, 3085, 16624]
]

def WDdata : List (List (List ℕ)) := [
  [[]],
  [[], [0]],
  [[], [0]],
  [[], [0]],
  [[], [0]],
  [[], [0]],
  [[], [0], [0, 0]],
  [[], [0], [0, 0]],
  [[], [0], [1], [0, 1]],
  [[], [0], [1], [0, 1]],
  [[], [0], [0, 0], [0, 0, 0]],
  [[], [0], [0, 0], [0, 0, 0]],
  [[], [0], [1], [0, 1]],
  [[], [0], [1], [0, 1]],
  [[], [0], [1], [0, 1]],
  [[], [0], [1], [0, 1]],
  [[], [0], [1], [0, 1]],
  [[], [0], [1], [0, 1]],
  [[], [0], [1], [0, 1]],
  [[], [0], [1], [0, 1]],
  [[], [0], [1], [0, 1]],
  [[], [0], [0, 0], [0, 0, 0]],
  [[], [0], [0, 0], [0, 0, 0]],
  [[], [0], [0, 0], [0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0, 0]],
  [[], [0], [0, 0], [0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0, 0]],
  [[], [0], [0, 0], [0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0, 0]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0]],
  [[], [0], [0, 0], [0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0, 0]],
  [[], [0], [1], [0, 0], [0, 1], [0, 0, 0], [0, 0, 1], [0, 0, 0, 1]],
  [[], [0], [1], [0, 0], [0, 1], [0, 0, 0], [0, 0, 1], [0, 0, 0, 1]],
  [[], [0], [1], [2], [0, 1], [0, 2], [1, 2], [0, 1, 2]],
  [[], [0], [1], [2], [0, 1], [0, 2], [1, 2], [0, 1, 2]],
  [[], [0], [1], [2], [0, 1], [0, 2], [1, 2], [0, 1, 2]],
  [[], [0], [1], [2], [0, 1], [0, 2], [1, 2], [0, 1, 2]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [0, 0, 0], [0, 0, 1]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [0, 0, 0], [0, 0, 1]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [0, 0, 0], [0, 0, 1]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [0, 0, 0], [0, 0, 1]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [0, 0, 0], [0, 0, 1]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [0, 0, 0], [0, 0, 1]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [0, 0, 0], [0, 0, 1]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [0, 0, 0], [0, 0, 1]],
  [[], [0], [1], [0, 0], [0, 1], [1, 1], [0, 0, 0], [0, 0, 1], [0, 1, 1], [1, 1, 1], [0, 0, 0, 1], [0, 1, 1, 1]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [0, 0, 0], [0, 0, 1], [1, 0, 0], [1, 0, 1], [0, 0, 0, 0], [0, 0, 0, 1]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [0, 0, 0], [0, 0, 1], [1, 0, 0], [1, 0, 1], [0, 0, 0, 0], [0, 0, 0, 1]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [0, 0, 0], [0, 0, 1], [1, 0, 0], [1, 0, 1], [0, 0, 0, 0], [0, 0, 0, 1]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [0, 0, 0], [0, 0, 1], [1, 0, 0], [1, 0, 1], [0, 0, 0, 0], [0, 0, 0, 1]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [0, 0, 0], [0, 0, 1], [1, 0, 0], [1, 0, 1], [0, 0, 0, 0], [0, 0, 0, 1]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [0, 0, 0], [0, 0, 1], [1, 0, 0], [1, 0, 1], [0, 0, 0, 0], [0, 0, 0, 1]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [0, 0, 0], [0, 0, 1], [1, 0, 0], [1, 0, 1], [0, 0, 0, 0], [0, 0, 0, 1]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1], [0, 0, 1], [0, 1, 0], [0, 1, 1], [0, 0, 1, 0], [0, 0, 1, 1]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1], [0, 0, 1], [0, 1, 1], [1, 0, 0], [1, 1, 0], [0, 1, 1, 0]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1], [0, 0, 1], [0, 1, 1], [1, 0, 0], [1, 1, 0], [0, 1, 1, 0]],
  [[], [0], [1], [2], [0, 0], [0, 1], [0, 2], [1, 2], [2, 0], [2, 1], [0, 0, 0], [0, 0, 1], [0, 0, 2], [0, 1, 2], [0, 2, 1], [0, 0, 0, 1]],
  [[], [0], [1], [2], [0, 0], [0, 1], [0, 2], [1, 2], [2, 0], [2, 1], [0, 0, 0], [0, 0, 1], [0, 0, 2], [0, 1, 2], [0, 2, 1], [0, 0, 0, 1]],
  [[], [0], [1], [2], [0, 0], [0, 1], [0, 2], [1, 1], [1, 2], [2, 0], [2, 1], [0, 0, 0], [0, 0, 1], [0, 0, 2], [0, 1, 1], [0, 1, 2], [0, 2, 1], [1, 1, 1], [1, 1, 2], [1, 2, 0], [0, 0, 0, 1], [0, 0, 0, 2], [0, 0, 2, 1], [0, 1, 1, 1]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1], [0, 0, 0], [0, 0, 1], [0, 1, 0], [0, 1, 1], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0], [0, 0, 1, 1], [0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1, 1]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1], [0, 0, 0], [0, 0, 1], [0, 1, 0], [0, 1, 1], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0], [0, 0, 1, 1], [0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1, 1]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1], [0, 0, 0], [0, 0, 1], [0, 1, 0], [0, 1, 1], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0], [0, 0, 1, 1], [0, 0, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1, 1]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1], [0, 0, 0], [0, 0, 1], [0, 1, 0], [0, 1, 1], [1, 0, 0], [1, 1, 0], [1, 1, 1], [0, 0, 0, 1], [0, 0, 1, 0], [0, 0, 1, 1], [0, 1, 0, 0], [0, 1, 1, 1], [1, 0, 0, 0], [1, 1, 1, 0], [0, 0, 0, 1, 0], [0, 1, 0, 0, 0], [0, 1, 1, 1, 0]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1], [0, 0, 0], [0, 0, 1], [0, 1, 0], [0, 1, 1], [1, 0, 0], [1, 1, 0], [1, 1, 1], [0, 0, 0, 1], [0, 0, 1, 0], [0, 0, 1, 1], [0, 1, 0, 0], [0, 1, 1, 1], [1, 0, 0, 0], [1, 1, 1, 0], [0, 0, 0, 1, 0], [0, 1, 0, 0, 0], [0, 1, 1, 1, 0]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1], [0, 0, 0], [0, 0, 1], [0, 1, 0], [0, 1, 1], [1, 0, 0], [1, 1, 0], [1, 1, 1], [0, 0, 0, 1], [0, 0, 1, 0], [0, 0, 1, 1], [0, 1, 0, 0], [0, 1, 1, 1], [1, 0, 0, 0], [1, 1, 1, 0], [0, 0, 0, 1, 0], [0, 1, 0, 0, 0], [0, 1, 1, 1, 0]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1], [0, 0, 0], [0, 0, 1], [0, 1, 0], [0, 1, 1], [1, 0, 0], [1, 1, 0], [1, 1, 1], [0, 0, 0, 1], [0, 0, 1, 0], [0, 0, 1, 1], [0, 1, 0, 0], [0, 1, 1, 1], [1, 0, 0, 0], [1, 1, 1, 0], [0, 0, 0, 1, 0], [0, 1, 0, 0, 0], [0, 1, 1, 1, 0]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1], [0, 0, 0], [0, 0, 1], [0, 1, 0], [0, 1, 1], [1, 0, 0], [1, 1, 0], [1, 1, 1], [0, 0, 0, 1], [0, 0, 1, 0], [0, 0, 1, 1], [0, 1, 0, 0], [0, 1, 1, 1], [1, 0, 0, 0], [1, 1, 1, 0], [0, 0, 0, 1, 0], [0, 1, 0, 0, 0], [0, 1, 1, 1, 0]],
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1], [0, 0, 0], [0, 0, 1], [0, 1, 0], [0, 1, 1], [1, 0, 0], [1, 1, 0], [1, 1, 1], [0, 0, 0, 1], [0, 0, 1, 0], [0, 0, 1, 1], [0, 1, 0, 0], [0, 1, 1, 1], [1, 0, 0, 0], [1, 1, 1, 0], [0, 0, 0, 1, 0], [0, 1, 0, 0, 0], [0, 1, 1, 1, 0]],
  [[], [0], [1], [2], [0, 0], [0, 1], [0, 2], [1, 0], [1, 1], [1, 2], [2, 0], [2, 1], [2, 2], [0, 0, 0], [0, 0, 1], [0, 0, 2], [0, 1, 0], [0, 1, 1], [0, 1, 2], [0, 2, 0], [0, 2, 1], [0, 2, 2], [1, 0, 2], [1, 1, 2], [1, 2, 1], [1, 2, 2], [2, 0, 0], [2, 0, 1], [2, 0, 2], [2, 1, 0], [2, 1, 1], [2, 1, 2], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 2], [0, 0, 1, 0], [0, 0, 1, 1], [0, 0, 1, 2], [0, 0, 2, 0], [0, 1, 0, 2], [0, 1, 1, 2], [0, 1, 2, 1], [0, 2, 1, 0], [0, 2, 1, 1], [0, 2, 1, 2], [1, 2, 1, 2], [0, 0, 0, 0, 1], [0, 0, 0, 1, 1]],
  [[], [0], [1], [2], [0, 0], [0, 1], [0, 2], [1, 0], [1, 1], [1, 2], [2, 0], [2, 1], [2, 2], [0, 0, 0], [0, 0, 1], [0, 0, 2], [0, 1, 0], [0, 1, 1], [0, 1, 2], [0, 2, 0], [0, 2, 1], [1, 0, 2], [1, 1, 2], [1, 2, 1], [2, 0, 0], [2, 0, 1], [2, 0, 2], [2, 1, 0], [2, 1, 1], [2, 1, 2], [2, 2, 0], [2, 2, 1], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 2], [0, 0, 1, 0], [0, 0, 1, 1], [0, 0, 1, 2], [0, 0, 2, 0], [0, 0, 2, 1], [0, 1, 0, 2], [0, 1, 1, 2], [0, 2, 0, 0], [0, 2, 0, 1], [0, 2, 0, 2], [0, 2, 1, 2], [0, 0, 0, 0, 0], [0, 0, 0, 0, 1]],
  [[], [0], [1], [2], [0, 0], [0, 1], [0, 2], [1, 0], [1, 1], [1, 2], [2, 0], [2, 1], [2, 2], [0, 0, 0], [0, 0, 1], [0, 0, 2], [0, 1, 0], [0, 1, 1], [0, 1, 2], [0, 2, 0], [0, 2, 1], [0, 2, 2], [1, 0, 2], [1, 1, 2], [1, 2, 2], [2, 0, 0], [2, 0, 1], [2, 0, 2], [2, 1, 0], [2, 1, 1], [2, 1, 2], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 2], [0, 0, 1, 0], [0, 0, 1, 1], [0, 0, 1, 2], [0, 0, 2, 0], [0, 1, 0, 2], [0, 1, 1, 2], [0, 2, 0, 0], [0, 2, 0, 1], [0, 2, 1, 2], [1, 0, 2, 0], [2, 0, 2, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [0, 0, 2, 0, 0]]
]

/-! ## The 73 representatives as explicit finite groups -/

/-- Decode a `9`-digit base-`3` code into a flat `3 × 3` matrix (row-major), entries in
`{-1, 0, 1}`. -/
def dec9 (c : ℕ) : List ℤ := (List.range 9).map fun i => ((c / 3 ^ i % 3 : ℕ) : ℤ) - 1

/-- Identity matrix, flat. -/
def one9 : List ℤ := [1, 0, 0, 0, 1, 0, 0, 0, 1]

/-- Product of the flat matrices selected by the word `w` (`getD` for out-of-range indices). -/
def wprod (gs : List (List ℤ)) (w : List ℕ) : List ℤ :=
  w.foldl (fun a i => m9mul a (gs.getD i [])) one9

/-- The explicit element list of the `j`-th arithmetic class, as flat matrices. -/
def ELc (j : Fin 73) : List (List ℤ) := (ELcodes.getD j.val []).map dec9

/-- The word (list of generator indices) attached to each element of `ELc j`. -/
def WD (j : Fin 73) : List (List ℕ) := WDdata.getD j.val []

/-- The explicit elements of the `j`-th arithmetic class, as matrices. -/
def EL (j : Fin 73) : List IMat := (ELc j).map imatOfList

/-- `EL j` as a `Finset`. -/
def finSet (j : Fin 73) : Finset IMat := (EL j).toFinset

/-! ### Kernel certificates -/

/-- Each list contains the identity. -/
theorem check_one : ∀ j : Fin 73, one9 ∈ ELc j := by decide

/-- Each list is closed under right multiplication by the generators of `arithRep j`. -/
theorem check_closed : ∀ j : Fin 73, ∀ e ∈ ELc j, ∀ g ∈ arithGens j,
    ∃ c ∈ ELcodes.getD j.val [], m9mul e g = dec9 c := by decide

/-- Each element carries a valid, short word evaluating to it. -/
theorem check_words : ∀ j : Fin 73, (WD j).length = (ELc j).length ∧
    ∀ i ∈ List.range (ELc j).length,
      (∀ k ∈ (WD j).getD i [], k < (arithGens j).length) ∧
      ((WD j).getD i []).length ≤ 48 ∧
      wprod (arithGens j) ((WD j).getD i []) = (ELc j).getD i [] := by decide

/-! ### Recursion lemmas for `sgClose` -/

theorem sgClose_zero (gens : List (List ℤ × List ℚ)) (acc : List (List ℤ × List ℚ)) :
    sgClose gens 0 acc = acc := rfl

private theorem sgClose_succ (gens : List (List ℤ × List ℚ)) (k : ℕ)
    (acc : List (List ℤ × List ℚ)) :
    sgClose gens (k + 1) acc
      = sgClose gens k (acc ++ acc.flatMap (fun a => gens.map fun g => sgMulPair a g)).dedup :=
  rfl

/-- `acc` is contained in every closure built on it. -/
theorem sgClose_subset_self (gens : List (List ℤ × List ℚ)) :
    ∀ (k : ℕ) (acc : List (List ℤ × List ℚ)), ∀ p ∈ acc, p ∈ sgClose gens k acc := by
  intro k
  induction k with
  | zero => intro acc p hp; rw [sgClose_zero]; exact hp
  | succ k ih =>
      intro acc p hp
      rw [sgClose_succ]
      exact ih _ p (List.mem_dedup.mpr (List.mem_append_left _ hp))

/-- `sgClose` is monotone in the starting list. -/
private theorem sgClose_mono_acc (gens : List (List ℤ × List ℚ)) :
    ∀ (k : ℕ) {acc acc' : List (List ℤ × List ℚ)}, (∀ p ∈ acc, p ∈ acc') →
      ∀ p ∈ sgClose gens k acc, p ∈ sgClose gens k acc' := by
  intro k
  induction k with
  | zero =>
      intro acc acc' h p hp
      rw [sgClose_zero] at hp ⊢
      exact h p hp
  | succ k ih =>
      intro acc acc' h p hp
      rw [sgClose_succ] at hp ⊢
      refine ih ?_ p hp
      intro q hq
      rw [List.mem_dedup] at hq ⊢
      rcases List.mem_append.mp hq with hq | hq
      · exact List.mem_append_left _ (h q hq)
      · obtain ⟨a, ha, hq⟩ := List.mem_flatMap.mp hq
        exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, h a ha, hq⟩)

/-- One more step only enlarges the closure. -/
private theorem sgClose_le_succ (gens : List (List ℤ × List ℚ)) (k : ℕ)
    (acc : List (List ℤ × List ℚ)) {p : List ℤ × List ℚ}
    (hp : p ∈ sgClose gens k acc) : p ∈ sgClose gens (k + 1) acc := by
  rw [sgClose_succ]
  refine sgClose_mono_acc gens k ?_ p hp
  intro q hq
  exact List.mem_dedup.mpr (List.mem_append_left _ hq)

/-- Monotonicity of `sgClose` in the number of steps. -/
theorem sgClose_le (gens : List (List ℤ × List ℚ)) :
    ∀ {k k' : ℕ}, k ≤ k' → ∀ (acc : List (List ℤ × List ℚ)) {p : List ℤ × List ℚ},
      p ∈ sgClose gens k acc → p ∈ sgClose gens k' acc := by
  intro k k' h
  induction h with
  | refl => intro acc p hp; exact hp
  | step _ ih => intro acc p hp; exact sgClose_le_succ gens _ acc (ih acc hp)

/-- The closure is closed under right multiplication by a generator. -/
theorem sgClose_mul (gens : List (List ℤ × List ℚ)) :
    ∀ (k : ℕ) (acc : List (List ℤ × List ℚ)), ∀ a ∈ sgClose gens k acc, ∀ g ∈ gens,
      sgMulPair a g ∈ sgClose gens (k + 1) acc := by
  intro k
  induction k with
  | zero =>
      intro acc a ha g hg
      rw [sgClose_succ, sgClose_zero]
      exact List.mem_dedup.mpr (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨g, hg, rfl⟩⟩))
  | succ k ih =>
      intro acc a ha g hg
      rw [sgClose_succ] at ha ⊢
      exact ih _ a ha g hg

/-! ### Words generate the closure -/

theorem intFract_zero : Int.fract (0 : ℚ) = 0 := by simp [Int.fract]

theorem m9vec_zero (a : List ℤ) : m9vec a [0, 0, 0] = [0, 0, 0] := by
  simp only [m9vec, List.range_succ_eq_map, List.range_zero, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.getD_cons_zero, List.getD_cons_succ,
    mul_zero, add_zero]

theorem sgMulPair_zero (a b : List ℤ) :
    sgMulPair (a, [0, 0, 0]) (b, [0, 0, 0]) = (m9mul a b, [0, 0, 0]) := by
  simp [sgMulPair, m9vec_zero]

theorem wprod_append (gs : List (List ℤ)) (w : List ℕ) (i : ℕ) :
    wprod gs (w ++ [i]) = m9mul (wprod gs w) (gs.getD i []) := by
  simp [wprod, List.foldl_append]

/-- A valid word evaluates to an element of the closure (with at least as much fuel). -/
theorem sgClose_mem_word (gens : List (List ℤ)) :
    ∀ (w : List ℕ), (∀ i ∈ w, i < gens.length) →
      (wprod gens w, [0, 0, 0]) ∈ sgClose (gens.map fun g => (g, [0, 0, 0])) w.length [sgOne] := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
      intro _
      rw [List.length_nil, sgClose_zero]
      exact List.mem_singleton_self _
  | append_singleton w i ih =>
      intro hw
      have hi : i < gens.length := hw i (List.mem_append_right _ (by simp))
      rw [List.length_append, List.length_singleton, wprod_append,
        List.getD_eq_getElem gens [] hi, ← sgMulPair_zero]
      exact sgClose_mul _ w.length [sgOne] _
        (ih (fun j hj => hw j (List.mem_append_left _ hj))) _
        (List.mem_map.mpr ⟨gens[i], List.getElem_mem hi, rfl⟩)

/-! ### The explicit lists coincide with `arithRep` -/

/-- Soundness: everything the generators reach inside the closure lies in the explicit list. -/
theorem sgClose_sound (gens : List (List ℤ)) (L : List (List ℤ))
    (hcl : ∀ e ∈ L, ∀ g ∈ gens, m9mul e g ∈ L) :
    ∀ (k : ℕ) (acc : List (List ℤ × List ℚ)), (∀ p ∈ acc, p.1 ∈ L) →
      ∀ p ∈ sgClose (gens.map fun g => (g, [0, 0, 0])) k acc, p.1 ∈ L := by
  intro k
  induction k with
  | zero =>
      intro acc h p hp
      rw [sgClose_zero] at hp
      exact h p hp
  | succ k ih =>
      intro acc h p hp
      rw [sgClose_succ] at hp
      refine ih _ ?_ p hp
      intro q hq
      rw [List.mem_dedup] at hq
      rcases List.mem_append.mp hq with hq | hq
      · exact h q hq
      · obtain ⟨a, ha, hq⟩ := List.mem_flatMap.mp hq
        obtain ⟨g', hg', hq'⟩ := List.mem_map.mp hq
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg'
        rw [← hq']
        exact hcl a.1 (h a ha) g0 hg0

theorem mem_finSet_iff {j : Fin 73} {A : IMat} :
    A ∈ finSet j ↔ ∃ e ∈ ELc j, A = imatOfList e := by
  rw [finSet, EL, List.mem_toFinset, List.mem_map]
  exact ⟨fun ⟨e, he, h⟩ => ⟨e, he, h.symm⟩, fun ⟨e, he, h⟩ => ⟨e, he, h.symm⟩⟩

theorem arithRep_subset_finSet (j : Fin 73) {A : IMat} (hA : A ∈ arithRep j) :
    A ∈ finSet j := by
  obtain ⟨p, hp, rfl⟩ := hA
  have hcl : ∀ e ∈ ELc j, ∀ g ∈ arithGens j, m9mul e g ∈ ELc j := by
    intro e he g hg
    obtain ⟨c, hc, hc'⟩ := check_closed j e he g hg
    exact List.mem_map.mpr ⟨c, hc, hc'.symm⟩
  have hinit : ∀ q ∈ ([sgOne] : List (List ℤ × List ℚ)), q.1 ∈ ELc j := by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact check_one j
  exact mem_finSet_iff.mpr ⟨p.1, sgClose_sound (arithGens j) (ELc j) hcl 48 _ hinit p hp, rfl⟩

theorem finSet_subset_arithRep (j : Fin 73) {A : IMat} (hA : A ∈ finSet j) :
    A ∈ arithRep j := by
  obtain ⟨e, he, rfl⟩ := mem_finSet_iff.mp hA
  obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.mp he
  have hcw := check_words j
  have hlen : i < (WD j).length := by rw [hcw.1]; exact hi
  have hspec := hcw.2 i (List.mem_range.mpr hi)
  have hvalid : ∀ k ∈ (WD j).getD i [], k < (arithGens j).length := hspec.1
  have hlen48 : ((WD j).getD i []).length ≤ 48 := hspec.2.1
  have hprod : wprod (arithGens j) ((WD j).getD i []) = (ELc j).getD i [] := hspec.2.2
  have hgetD : (ELc j).getD i [] = e := by
    rw [List.getD_eq_getElem _ _ hi]; exact hie
  have hmem := sgClose_mem_word (arithGens j) ((WD j).getD i []) hvalid
  rw [hprod, hgetD] at hmem
  exact ⟨(e, [0, 0, 0]), sgClose_le _ hlen48 [sgOne] hmem, rfl⟩

/-- The explicit list `finSet j` is exactly the `j`-th arithmetic-class representative. -/
theorem mem_arithRep (j : Fin 73) (A : IMat) : A ∈ arithRep j ↔ A ∈ finSet j :=
  ⟨fun h => arithRep_subset_finSet j h, fun h => finSet_subset_arithRep j h⟩

/-! ## A conjugation invariant -/

/-- Reduction of an integer matrix modulo `m`. -/
def redmod (m : ℕ) (A : IMat) : Matrix (Fin 3) (Fin 3) (ZMod m) :=
  A.map (Int.castRingHom (ZMod m))

/-- Action of an integer matrix on `(ℤ/m)³`. -/
def actm (m : ℕ) (A : IMat) (v : Fin 3 → ZMod m) : Fin 3 → ZMod m :=
  (redmod m A).mulVec v

/-- Number of elements of `P` fixing the vector `v` of `(ℤ/m)³`. -/
def nfix (m : ℕ) (P : Finset IMat) (v : Fin 3 → ZMod m) : ℕ :=
  (P.filter (fun A => actm m A v = v)).card

/-- Power sum of the traces of the elements of `P`. -/
def trPow (P : Finset IMat) (k : ℕ) : ℤ :=
  ∑ A ∈ P, A.trace ^ k

/-- Power sum of the numbers of fixed vectors of the `(ℤ/m)³`-action of `P`. -/
def fixPow (m : ℕ) [NeZero m] (P : Finset IMat) (k : ℕ) : ℤ :=
  ∑ v : Fin 3 → ZMod m, ((nfix m P v : ℤ)) ^ k

/-- A conjugation invariant of a finite set of integer matrices: the cardinality, the first three
power sums of the traces, and the first two power sums of the numbers of fixed vectors of the
actions on `(ℤ/2)³`, `(ℤ/3)³` and `(ℤ/4)³`. -/
def invOf (P : Finset IMat) : List ℤ :=
  [(P.card : ℤ), trPow P 1, trPow P 2, trPow P 3,
   fixPow 2 P 1, fixPow 2 P 2, fixPow 3 P 1, fixPow 3 P 2, fixPow 4 P 1, fixPow 4 P 2]

/-- The invariant separates the 73 representatives. -/
theorem invOf_nodup : (List.ofFn fun j : Fin 73 => invOf (finSet j)).Nodup := by decide

/-- The invariant is injective on the 73 representatives. -/
theorem invOf_injective : Function.Injective (fun j : Fin 73 => invOf (finSet j)) := by
  intro j j' h
  have hnd := invOf_nodup
  have h1 : j.val < (List.ofFn fun i : Fin 73 => invOf (finSet i)).length := by simp
  have h2 : j'.val < (List.ofFn fun i : Fin 73 => invOf (finSet i)).length := by simp
  have heq : (List.ofFn fun i : Fin 73 => invOf (finSet i))[j.val]
      = (List.ofFn fun i : Fin 73 => invOf (finSet i))[j'.val] := by
    rw [List.getElem_ofFn, List.getElem_ofFn]
    exact h
  exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp heq)

end Work.SG
