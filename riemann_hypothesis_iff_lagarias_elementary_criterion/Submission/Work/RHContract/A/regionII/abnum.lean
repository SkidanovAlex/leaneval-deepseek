import Mathlib
import Submission.Work.RHContract.A.regionII.abdefs

/-!
# Region II, part A: the rational bounds used in the final numeric check

All constants below are explicit rationals chosen so that the following real inequalities
hold (the bracketing lemmas `ThetaBracket.ltOf_le_log` / `log_le_utOf` supply them, and the
values are the ones returned by `ltOf`/`utOf` at the indicated arguments):

* `log173 ≥ 5153259971/10^9`, `log273 ≥ 5609470336/10^9`, `log513 ≥ 6240274220/10^9`
  (chords for `log`), `log274 ≤ 5613282966/10^9`, `log512 ≤ 6238440000/10^9`
  (tangents for `log`), `log2.5 ≤ 918173/10^6 = (utOf 5 − ltOf 2)/10^9`,
  `log(10^5) ≤ 11525819454/10^9`, `log30000 ≥ 10308020696/10^9`,
  `log501 ≥ 6215068509/10^9`;
* `√173 ≥ 1315/100`, `√273 ≥ 1652271/10^5`, `√274 ≥ 16552945/10^6`, `√501 ≥ 22383/10^3 = 22.383`,
  `√501 ≤ 2238310/10^5`, `√30000 ≥ 1732/10`, `1/√2.5 ≤ 632454/10^6`.

The bound functions are

* `caUbd n` : upper bound for `(36/100)·caU ξ`, using `ξ ≥ 30000` in the branch `n ≤ 274`
  and `ξ ≥ (n−1)²/2.5` otherwise (so `√ξ ≥ (n−1)/√2.5`, `log ξ ≥ 2log(n−1) − log 2.5`);
* `abAbd n`: upper bound for `abA n`: the denominators use the lower bounds `logl n ≤ log n`
  and `sqL n ≤ √n`, the `u` terms use `logU n ≥ log n` for `u(n) ≤ 1/(n logU n)` and
  `u501u ≥ u(501)`, `u501l ≤ u(501)`;
* `abJbd`  : lower bound for `abJ ξ` for `ξ ∈ [30000, 10^5]`.
-/

set_option maxHeartbeats 0

namespace Work.RHContract.A.RegionII

noncomputable section

/-- `log 173` lower bracket (ltOf 173). -/
def lg173 : ℝ := 5153259971 / 10 ^ 9
/-- `log 273` lower bracket (ltOf 273). -/
def lg273 : ℝ := 5609470336 / 10 ^ 9
/-- `log 513` lower bracket (ltOf 513). -/
def lg513 : ℝ := 6240274220 / 10 ^ 9
/-- `log 274` upper bracket (utOf 274). -/
def lg274u : ℝ := 5613282966 / 10 ^ 9
/-- `log 512` upper bracket (utOf 512). -/
def lg512u : ℝ := 6238440000 / 10 ^ 9
/-- `log 2.5` upper bracket `= (utOf 5 − ltOf 2)/10^9`. -/
def lg25u : ℝ := (1611320000 - 693147000 : ℝ) / 10 ^ 9
/-- `1/√2.5` lower bracket. -/
def inv25 : ℝ := 632454 / 10 ^ 6
/-- `√173` lower bracket. -/
def sq173l : ℝ := 1315 / 100
/-- `√273` lower bracket. -/
def sq273l : ℝ := 1652271 / 10 ^ 5
/-- `√274` lower bracket. -/
def sq274l : ℝ := 16552945 / 10 ^ 6
/-- `√501` lower bracket (`≤ √501`). -/
def sq501l : ℝ := 22383 / 10 ^ 3
/-- `√501` upper bracket (`≥ √501`). -/
def sq501u : ℝ := 2238310 / 10 ^ 5
/-- `√30000` lower bracket. -/
def sq30000l : ℝ := 1732 / 10
/-- `log (10^5)` upper bracket. -/
def lg100ku : ℝ := 11525819454 / 10 ^ 9
/-- `log 30000` lower bracket. -/
def lg30000l : ℝ := 10308020696 / 10 ^ 9
/-- `log 501` lower bracket. -/
def lg501l : ℝ := 6215068509 / 10 ^ 9
/-- `u(501) = 1/(501 log 501)` lower bracket. -/
def u501l : ℝ := 1 / (501 * lg512u)
/-- `u(501)` upper bracket. -/
def u501u : ℝ := 1 / (501 * lg501l)
/-- `u(30000)` upper bracket. -/
def uzu : ℝ := 1 / (30000 * lg30000l)
/-- `u(10^5)` lower bracket. -/
def uzl : ℝ := 1 / (10 ^ 5 * lg100ku)
/-- `χ(501)` upper bracket. -/
def chi501u : ℝ := (2 + 1 / lg501l) / lg501l
/-- `501^{-3/2}` lower bracket. -/
def inv501_32_lb : ℝ := 1 / (501 * sq501u)
/-- `501^{-3/2}` upper bracket. -/
def inv501_32_ub : ℝ := 1 / (501 * sq501l)

/-- Chord for `log(n−1)`, `n ∈ [274,514]`. -/
def chordA (n : ℕ) : ℝ := lg273 + ((n : ℝ) - 274) * (lg513 - lg273) / 240
/-- Chord for `log n`, `n ∈ [173,273]`. -/
def chordB (n : ℕ) : ℝ := lg173 + ((n : ℝ) - 173) * (lg273 - lg173) / 100
/-- Lower bound for `log n`. -/
def logl (n : ℕ) : ℝ := if n ≤ 273 then chordB n else chordA n
/-- Upper bound for `log n` (min of the two tangents at `274` and `512`). -/
def logU (n : ℕ) : ℝ :=
  if n ≤ 368 then lg274u + ((n : ℝ) - 274) / 274 else lg512u + ((n : ℝ) - 512) / 512
/-- Lower bound for `√n` (chord on `[173,273]` or on `[274,501]`). -/
def sqL (n : ℕ) : ℝ :=
  if n ≤ 273 then sq173l + ((n : ℝ) - 173) * (sq273l - sq173l) / 100
  else sq274l + ((n : ℝ) - 274) * (sq501l - sq274l) / 227
/-- Upper bound for `χ n = (2 + 1/log n)/log n`. -/
def chiU (n : ℕ) : ℝ := (2 + 1 / logl n) / logl n
/-- Upper bound for `(36/100)·caU ξ`. -/
def caUbd (n : ℕ) : ℝ :=
  if n ≤ 274 then (36 / 100) / (sq30000l * lg30000l)
  else (36 / 100) / (((n : ℝ) - 1) * inv25 * (2 * chordA n - lg25u))
/-- Upper bound for `abA n`. -/
def abAbd (n : ℕ) : ℝ :=
  (1 - (64 / 100) / sq501u) / ((n : ℝ) * logl n)
    - (2 / ((n : ℝ) * logU n) - 2 * u501u
        - (1 / ((n : ℝ) * logl n) - u501l) / (logl n + 1)
        - (189 / 100) * chiU n * (2 / 3) * (1 / ((n : ℝ) * sqL n) - inv501_32_lb)
        - chiU n / 2 * (1 / ((n : ℝ)) ^ 2 - 1 / (501 : ℝ) ^ 2))
/-- Lower bound for `abJ ξ`, `ξ ∈ [30000, 10^5]`. -/
def abJbd : ℝ :=
  (96 / 100) / (10 ^ 5 * lg100ku) + 2 * (u501l - uzu) - (u501u - uzl) / (lg501l + 1)
    - (23 / 10) * chi501u * (2 / 3) * inv501_32_ub

end

end Work.RHContract.A.RegionII
