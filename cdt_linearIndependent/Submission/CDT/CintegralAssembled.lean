import Mathlib
import Submission.CDT.CintegralFour
import Submission.CDT.CintegralFive
import Submission.CDT.CintegralSix
import Submission.CDT.CintegralSeven
import Submission.CDT.CintegralEight
import Submission.CDT.CintegralNine
import Submission.CDT.CintegralTen
import Submission.CDT.CintegralEleven
import Submission.CDT.CintegralTwelve
import Submission.CDT.CintegralThirteen
import Submission.CDT.CintegralFourteen
import Submission.CDT.CintegralFifteen
import Submission.CDT.CintegralSixteen
import Submission.CDT.CintegralSeventeen
import Submission.CDT.CintegralEighteen
import Submission.CDT.CintegralNineteen
import Submission.CDT.CintegralTwenty
import Submission.CDT.CintegralTwentyOne
import Submission.CDT.CintegralTwentyTwo
import Submission.CDT.CintegralTwentyThree
import Submission.CDT.CintegralTwentyFour
import Submission.CDT.CintegralTwentyFive
import Submission.CDT.CintegralTwentySix
import Submission.CDT.CintegralTwentySeven
import Submission.CDT.CintegralTwentyEight
import Submission.CDT.CintegralTwentyNine
import Submission.CDT.CintegralThirty
import Submission.CDT.CintegralThirtyOne
import Submission.CDT.CintegralThirtyTwo
import Submission.CDT.CintegralThirtyThree
import Submission.CDT.CintegralThirtyFour
import Submission.CDT.CintegralThirtyFive
import Submission.Commons.Analysis.Integral.cintegral_recurrence_parametric
import Submission.CDT.CintegralOne
import Submission.CDT.L2chi3Cintegral
import Submission.CDT.ZagierH
import Submission.CDT.ZagierHBC
import Submission.CDT.EichlerInput

/-!
# Assembled `(Cintegral)` instances through `n = 35`

The per-degree modules `CintegralOne`–`CintegralTwentyThree` each close one
instance `CintegralIdentityAt n` of the Beukers double-integral identity
`L(2,χ₋₃)·aₙ − 2·bₙ = Jₙ` (`J₀ = L`, `J₁ = 3L − 2`, `J₂ = 15L − 23/2`,
`J₃ = 93L − 145/2`, `J₄ = 639L − 3993/8`, `J₅ = 4653L − 727059/200`,
`J₆ = 35169L − 5495507/200`, `J₇ = 272835L − 417806469/1960`,
`J₈ = 2157759L − 66085799967/39200`, `J₉ = 17319837L − 530455590781/39200`,
`J₁₀ = 140668065L − 4308248502993/39200`,
`J₁₁ = 1153462995L − 4274588067098379/4743200`,
`J₁₂ = 9533639025L − 1413218448827853/189728`,
`J₁₃ = 79326566595L − 49681644752988856791/801600800`,
`J₁₄ = 663835030335L − 415754993154999572883/801600800`,
`J₁₅ = 5582724468093L − 699283848231726007461/160320160`,
`J₁₆ = 47152425626559L − 2147724879365145978567/58298240`,
`J₁₇ = 399769750195965L − 11577240673264126122251355/37066020992`,
`J₁₈ = 3400775573443089L − 492428419986863926518413443/185330104960`,
`J₁₉ = 29016970072920387L − 1516786312598844261610104459489/66904167890560`,
`J₂₀ = 248256043372999089L − 64884680871542898537412147933623/334520839452800`,
`J₂₁ = 2129158861755559587L − 556481088608425410076556411551509/334520839452800`,
`J₂₂ = 18301184259810988815L − 956646600932891283673112179939701/66904167890560`,
`J₂₃ = 157626238006835196237L − 21793477080637841759891355106455157611/176961524070531200`,
`J₂₄ = 1360135024740956026161L − 188052901998329938720023301915553943483/176961524070531200`,
`J₂₅ = 11756409817108040588403L − 125808567865009046495730414430613843427/13696712389360000`,
`J₂₆ = 101776883914919689791759L − 351792984306704939720912856563287360631613/4424038101763280000`,
`J₂₇ = 882377309200542746869245L − 55453589879044465247580079582818458420113/80437056395696000`,
`J₂₈ = 7660282466987138660520879L − 26477855540816887598470329785402234290329453/4424038101763280000`,
`J₂₉ = 66585517462089771364449117L − 193559191397796001889093611562322161796668693679/3720616043582918480000`,
`J₃₀ = 579458978311046252959242369L − 1684444539369042247492198290598164527862801209403/3720616043582918480000`,
`J₃₁ = 5048245768766634904503427587L − 742239899969897495427276970725258689060769643804011/188184843046483403120000` — the `aₙ` are Zagier's
`A = 10, B = 9` Apéry-like numbers, the `bₙ` the `H_B`-companion
denominators).  This module assembles them into the uniform statements

```lean
theorem cintegral_identity_le_thirtyFive : ∀ n : ℕ, n ≤ 35 → CintegralIdentityAt n
theorem cintegral_identity_le_eight : ∀ n : ℕ, n ≤ 8 → CintegralIdentityAt n
theorem cintegral_identity_le_ten   : ∀ n : ℕ, n ≤ 10 → CintegralIdentityAt n
theorem cintegral_identity_le_twelve: ∀ n : ℕ, n ≤ 12 → CintegralIdentityAt n
theorem cintegral_identity_le_fourteen: ∀ n : ℕ, n ≤ 14 → CintegralIdentityAt n
theorem cintegral_identity_le_sixteen: ∀ n : ℕ, n ≤ 16 → CintegralIdentityAt n
theorem cintegral_identity_le_seventeen: ∀ n : ℕ, n ≤ 17 → CintegralIdentityAt n
theorem cintegral_identity_le_nineteen : ∀ n : ℕ, n ≤ 19 → CintegralIdentityAt n
theorem cintegral_identity_le_twenty   : ∀ n : ℕ, n ≤ 20 → CintegralIdentityAt n
theorem cintegral_identity_le_twentyOne: ∀ n : ℕ, n ≤ 21 → CintegralIdentityAt n
```

i.e. the first thirty-six instances of `CintegralIdentity` (the missing tail
`CintegralIdentityTail` = the instances at all `n ≥ 2` — equivalently
`n ≥ 18` — is the object of the parametric/creative-telescoping stroke
recorded in the `L2chi3Cintegral` roadmap; the commons identities
`sum_cintegral{One,..,Seventeen}_core` are committed and the module generator
(`Scratch/cintegral_generator/mkmod3.py`) produces the next-degree modules
mechanically).

**Parametric reductions (the two ways to close the tail at once).**  Two
proved reductions isolate the remaining analytic input:
* `CintegralIdentity_of_recurrence` — the whole of `CintegralIdentity`
  follows from the single Zagier three-term recurrence
  `(n+1)²J_{n+1} = (10n²+10n+3)Jₙ − 9n²J_{n−1}` (`n ≥ 1`) for the double
  integrals `Jₙ = cintegralJ n`: both `J` and `cₙ = L·aₙ − 2·bₙ` satisfy
  that recurrence (`zagier_diff_recurrence`) and a sequence satisfying it
  is determined by its first two values (`eq_of_zagier_recurrence`), the
  base cases `n = 0, 1` being PROVED.  Consequently
  `overconvergesB_of_recurrence` (and
  `eichlerInputB_of_modular_and_recurrence`) reduce the analytic conjunct of
  `EichlerInputB` to that recurrence.
* **the per-degree modules are now *light* bridges** (~90 lines each,
  generated by `Scratch/cintegral_generator/mklight_all.py`): for every
  degree `2 ≤ n ≤ 23` the module `Cintegral<Deg>` proves
  `CintegralIdentityAt n` from the general expansion below plus the commons
  core `sum_cintegral<Deg>_core` for that degree.  The earlier ~800-line
  per-degree analytic modules (which evaluated `Jₙ = Σₘ Wₙ(m)` inside the
  module by binomial series + two Bochner interchanges + monomial integrals,
  for `n ≤ 19`) are superseded and archived in `Scratch/archive_heavy/`;
* **module `Submission.CDT.CintegralGeneral`** proves the general-`n`
  statement `cintegralJ_eq_sum_W_gen : ∀ n, cintegralJ n = ∑' m, genW n m`
  with the parametric summand
  `genW n m = 9ⁿ·C(m+2n,2n)·Σᵢ₌₀^{2n+1}(−1)ⁱC(2n+1,i)·(3ⁿn!/∏_{k≤n}(3m+n+1+3k+i))²`
  (the general Beukers expansion), *plus* the summability `genW_summable`
  and the reduction `CintegralIdentity_of_genW_sum`: the whole identity
  follows from the single parametric `m`-sum evaluation
  `∀n, Σ'ₘ genW n m = L(2,χ₋₃)aₙ − 2bₙ` (the definitions of
  `CintegralGeneral` were checked to reproduce the per-degree ones at
  `n = 2, 3`);
* the per-degree modules supply, for every proved instance, the general
  shape `Jₙ = Σₘ Wₙ(m)`
  (`Wₙ(m) = 9ⁿ·C(m+2n,2n)·Σᵢ₌₀^{2n+1}(−1)ⁱC(2n+1,i)·Mₙ(3m+n+i)²`,
  `Mₙ(q) = 3ⁿn!/∏_{k≤n}(q+1+3k)`), whose `m`-sum is evaluated by the
  commons creative-telescoping cores `sum_cintegral{One,..,TwentyOne}_core`.

**A recorded obstruction for the "n-polynomial" divergence certificate.**
A natural attempt at the recurrence is to look for a pointwise
divergence identity `∂_s(uP) + ∂_t(uQ) = G(n,u)/R` on the square, with
`u = 9st(1−s³)(1−t³)/(1+st+s²t²)²`, `R = 1+st+s²t²`,
`G(n,u) = 9(n+1)²u² − (10n²+10n+3)u + n²` and `P, Q` polynomials in `n`
with `(s,t)`-coefficients: separating the `n`-powers would force each
component `g_k(u)/R` (`g₂ = 9u²−10u+1`, `g₁ = 18u²−10u`,
`g₀ = 9u²−3u`) to be a divergence with vanishing boundary values, hence
`∫∫g_k(u)/R = 0`; but `∫∫g₂(u)/R = J₂/9 − 10J₁/9 + J₀
= 17/18 − 2L/3 ≠ 0` (using the PROVED instances `J₀, J₁, J₂`).  So no such
certificate exists: the certificate must be genuinely `x`-dependent
(denominators `(R² − 9Wx)`), or the recurrence must be approached
parametrically on the `Wₙ(m)` summands.

**Note on the parametric stroke.**  A direct divergence-form /
integration-by-parts certificate for the Zagier recurrence
`(n+1)²J_{n+1} = (10n²+10n+3)Jₙ − 9n²J_{n−1}` on the kernel family
`Kₙ(s,t) = 9ⁿ(st)ⁿ(1−s³)ⁿ(1−t³)ⁿ/(1+st+s²t²)^{2n+1}` was searched for in a
symmetric ansatz `W(u)` (`u = 9st(1−s³)(1−t³)/(1+st+s²t²)²`, low-degree
rational `W`) and does **not** exist at low degree: the two-dimensional
creative telescoping certificate is genuinely non-trivial (the per-degree
identities `sum_cintegral{N}_core` are all proved by the fleet independently).
So the tail is currently closed degree-by-degree rather than parametrically.
-/

noncomputable section

open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Interval

namespace Submission.CDT

/-- **first instances of `CintegralIdentity`**: `CintegralIdentityAt n` for
every `n ≤ 8` (assembled from the zero/one/two/three/four/five/six/seven/
eight instances). -/
theorem cintegral_identity_le_eight : ∀ n : ℕ, n ≤ 8 → CintegralIdentityAt n := by
  intro n hn
  interval_cases n
  · change L2chi3Real * (HA_coeff 0 : ℝ) - 2 * (HB_coeff 0 : ℝ) = cintegralJ 0
    exact CintegralIdentity_zero
  · change L2chi3Real * (HA_coeff 1 : ℝ) - 2 * (HB_coeff 1 : ℝ) = cintegralJ 1
    exact cintegral_identity_one
  · change L2chi3Real * (HA_coeff 2 : ℝ) - 2 * (HB_coeff 2 : ℝ) = cintegralJ 2
    exact CintegralIdentityAt_two
  · change L2chi3Real * (HA_coeff 3 : ℝ) - 2 * (HB_coeff 3 : ℝ) = cintegralJ 3
    exact CintegralIdentityAt_three
  · change L2chi3Real * (HA_coeff 4 : ℝ) - 2 * (HB_coeff 4 : ℝ) = cintegralJ 4
    exact CintegralIdentityAt_four
  · change L2chi3Real * (HA_coeff 5 : ℝ) - 2 * (HB_coeff 5 : ℝ) = cintegralJ 5
    exact CintegralIdentityAt_five
  · change L2chi3Real * (HA_coeff 6 : ℝ) - 2 * (HB_coeff 6 : ℝ) = cintegralJ 6
    exact CintegralIdentityAt_six
  · change L2chi3Real * (HA_coeff 7 : ℝ) - 2 * (HB_coeff 7 : ℝ) = cintegralJ 7
    exact CintegralIdentityAt_seven
  · change L2chi3Real * (HA_coeff 8 : ℝ) - 2 * (HB_coeff 8 : ℝ) = cintegralJ 8
    exact CintegralIdentityAt_eight

/-- the instances through `n = 7` (subset of `cintegral_identity_le_eight`) -/
theorem cintegral_identity_le_seven : ∀ n : ℕ, n ≤ 7 → CintegralIdentityAt n := by
  intro n hn
  exact cintegral_identity_le_eight n (by omega)

/-- the instances through `n = 9` -/
theorem cintegral_identity_le_nine : ∀ n : ℕ, n ≤ 9 → CintegralIdentityAt n := by
  intro n hn
  by_cases h : n ≤ 8
  · exact cintegral_identity_le_eight n h
  · interval_cases n
    · change L2chi3Real * (HA_coeff 9 : ℝ) - 2 * (HB_coeff 9 : ℝ) = cintegralJ 9
      exact CintegralIdentityAt_nine

/-- the instances through `n = 10` -/
theorem cintegral_identity_le_ten : ∀ n : ℕ, n ≤ 10 → CintegralIdentityAt n := by
  intro n hn
  by_cases h : n ≤ 9
  · exact cintegral_identity_le_nine n h
  · interval_cases n
    · change L2chi3Real * (HA_coeff 10 : ℝ) - 2 * (HB_coeff 10 : ℝ) = cintegralJ 10
      exact CintegralIdentityAt_ten

/-- the instances through `n = 11` -/
theorem cintegral_identity_le_eleven : ∀ n : ℕ, n ≤ 11 → CintegralIdentityAt n := by
  intro n hn
  by_cases h : n ≤ 10
  · exact cintegral_identity_le_ten n h
  · interval_cases n
    · change L2chi3Real * (HA_coeff 11 : ℝ) - 2 * (HB_coeff 11 : ℝ) = cintegralJ 11
      exact CintegralIdentityAt_eleven

/-- the instances through `n = 12` -/
theorem cintegral_identity_le_twelve : ∀ n : ℕ, n ≤ 12 → CintegralIdentityAt n := by
  intro n hn
  by_cases h : n ≤ 11
  · exact cintegral_identity_le_eleven n h
  · interval_cases n
    · change L2chi3Real * (HA_coeff 12 : ℝ) - 2 * (HB_coeff 12 : ℝ) = cintegralJ 12
      exact CintegralIdentityAt_twelve

/-- the instances through `n = 13` -/
theorem cintegral_identity_le_thirteen : ∀ n : ℕ, n ≤ 13 → CintegralIdentityAt n := by
  intro n hn
  by_cases h : n ≤ 12
  · exact cintegral_identity_le_twelve n h
  · interval_cases n
    · change L2chi3Real * (HA_coeff 13 : ℝ) - 2 * (HB_coeff 13 : ℝ) = cintegralJ 13
      exact CintegralIdentityAt_thirteen

/-- the instances through `n = 14` -/
theorem cintegral_identity_le_fourteen : ∀ n : ℕ, n ≤ 14 → CintegralIdentityAt n := by
  intro n hn
  by_cases h : n ≤ 13
  · exact cintegral_identity_le_thirteen n h
  · interval_cases n
    · change L2chi3Real * (HA_coeff 14 : ℝ) - 2 * (HB_coeff 14 : ℝ) = cintegralJ 14
      exact CintegralIdentityAt_fourteen

/-- the instances through `n = 15` -/
theorem cintegral_identity_le_fifteen : ∀ n : ℕ, n ≤ 15 → CintegralIdentityAt n := by
  intro n hn
  by_cases h : n ≤ 14
  · exact cintegral_identity_le_fourteen n h
  · interval_cases n
    · change L2chi3Real * (HA_coeff 15 : ℝ) - 2 * (HB_coeff 15 : ℝ) = cintegralJ 15
      exact CintegralIdentityAt_fifteen

/-- the instances through `n = 16` -/
theorem cintegral_identity_le_sixteen : ∀ n : ℕ, n ≤ 16 → CintegralIdentityAt n := by
  intro n hn
  by_cases h : n ≤ 15
  · exact cintegral_identity_le_fifteen n h
  · interval_cases n
    · change L2chi3Real * (HA_coeff 16 : ℝ) - 2 * (HB_coeff 16 : ℝ) = cintegralJ 16
      exact CintegralIdentityAt_sixteen

/-- the instances through `n = 17` -/
theorem cintegral_identity_le_seventeen : ∀ n : ℕ, n ≤ 17 → CintegralIdentityAt n := by
  intro n hn
  by_cases h : n ≤ 16
  · exact cintegral_identity_le_sixteen n h
  · interval_cases n
    · change L2chi3Real * (HA_coeff 17 : ℝ) - 2 * (HB_coeff 17 : ℝ) = cintegralJ 17
      exact CintegralIdentityAt_seventeen

/-- the instances through `n = 18` -/
theorem cintegral_identity_le_eighteen : ∀ n : ℕ, n ≤ 18 → CintegralIdentityAt n := by
  intro n hn
  by_cases h : n ≤ 17
  · exact cintegral_identity_le_seventeen n h
  · interval_cases n
    · change L2chi3Real * (HA_coeff 18 : ℝ) - 2 * (HB_coeff 18 : ℝ) = cintegralJ 18
      exact CintegralIdentityAt_eighteen

/-- the instances through `n = 19` -/
theorem cintegral_identity_le_nineteen : ∀ n : ℕ, n ≤ 19 → CintegralIdentityAt n := by
  intro n hn
  by_cases h : n ≤ 18
  · exact cintegral_identity_le_eighteen n h
  · interval_cases n
    · change L2chi3Real * (HA_coeff 19 : ℝ) - 2 * (HB_coeff 19 : ℝ) = cintegralJ 19
      exact CintegralIdentityAt_nineteen

/-- the instances through `n = 20` -/
theorem cintegral_identity_le_twenty : ∀ n : ℕ, n ≤ 20 → CintegralIdentityAt n := by
  intro n hn
  by_cases h : n ≤ 19
  · exact cintegral_identity_le_nineteen n h
  · interval_cases n
    · change L2chi3Real * (HA_coeff 20 : ℝ) - 2 * (HB_coeff 20 : ℝ) = cintegralJ 20
      exact CintegralIdentityAt_twenty

/-- the instances through `n = 21` -/
theorem cintegral_identity_le_twentyOne : ∀ n : ℕ, n ≤ 21 → CintegralIdentityAt n := by
  intro n hn
  by_cases h : n ≤ 20
  · exact cintegral_identity_le_twenty n h
  · interval_cases n
    · change L2chi3Real * (HA_coeff 21 : ℝ) - 2 * (HB_coeff 21 : ℝ) = cintegralJ 21
      exact CintegralIdentityAt_twentyone

/-- the instances through `n = 22` -/
theorem cintegral_identity_le_twentyTwo : ∀ n : ℕ, n ≤ 22 → CintegralIdentityAt n := by
  intro n hn
  by_cases h : n ≤ 21
  · exact cintegral_identity_le_twentyOne n h
  · interval_cases n
    · change L2chi3Real * (HA_coeff 22 : ℝ) - 2 * (HB_coeff 22 : ℝ) = cintegralJ 22
      exact CintegralIdentityAt_twentytwo

/-- the instances through `n = 23` -/
theorem cintegral_identity_le_twentyThree : ∀ n : ℕ, n ≤ 23 → CintegralIdentityAt n := by
  intro n hn
  by_cases h : n ≤ 22
  · exact cintegral_identity_le_twentyTwo n h
  · interval_cases n
    · change L2chi3Real * (HA_coeff 23 : ℝ) - 2 * (HB_coeff 23 : ℝ) = cintegralJ 23
      exact CintegralIdentityAt_twentythree

/-- the instances through `n = 24` -/
theorem cintegral_identity_le_twentyFour : ∀ n : ℕ, n ≤ 24 → CintegralIdentityAt n := by
  intro n hn
  by_cases h : n ≤ 23
  · exact cintegral_identity_le_twentyThree n h
  · interval_cases n
    · change L2chi3Real * (HA_coeff 24 : ℝ) - 2 * (HB_coeff 24 : ℝ) = cintegralJ 24
      exact CintegralIdentityAt_twentyfour

/-- the instances through `n = 25` -/
theorem cintegral_identity_le_twentyFive : ∀ n : ℕ, n ≤ 25 → CintegralIdentityAt n := by
  intro n hn
  by_cases h : n ≤ 24
  · exact cintegral_identity_le_twentyFour n h
  · interval_cases n
    · change L2chi3Real * (HA_coeff 25 : ℝ) - 2 * (HB_coeff 25 : ℝ) = cintegralJ 25
      exact CintegralIdentityAt_twentyfive

/-- the instances through `n = 26` -/
theorem cintegral_identity_le_twentySix : ∀ n : ℕ, n ≤ 26 → CintegralIdentityAt n := by
  intro n hn
  by_cases h : n ≤ 25
  · exact cintegral_identity_le_twentyFive n h
  · interval_cases n
    · change L2chi3Real * (HA_coeff 26 : ℝ) - 2 * (HB_coeff 26 : ℝ) = cintegralJ 26
      exact CintegralIdentityAt_twentysix

/-- the instances through `n = 27` -/
theorem cintegral_identity_le_twentySeven : ∀ n : ℕ, n ≤ 27 → CintegralIdentityAt n := by
  intro n hn
  by_cases h : n ≤ 26
  · exact cintegral_identity_le_twentySix n h
  · interval_cases n
    · change L2chi3Real * (HA_coeff 27 : ℝ) - 2 * (HB_coeff 27 : ℝ) = cintegralJ 27
      exact CintegralIdentityAt_twentyseven

/-- the instances of `CintegralIdentity` through `n = 28` -/
theorem cintegral_identity_le_twentyEight : ∀ n : ℕ, n ≤ 28 → CintegralIdentityAt n := by
  intro n hn
  by_cases h : n ≤ 27
  · exact cintegral_identity_le_twentySeven n h
  · interval_cases n
    · change L2chi3Real * (HA_coeff 28 : ℝ) - 2 * (HB_coeff 28 : ℝ) = cintegralJ 28
      exact CintegralIdentityAt_twentyeight

/-- the instances of `CintegralIdentity` through `n = 29` -/
theorem cintegral_identity_le_twentyNine : ∀ n : ℕ, n ≤ 29 → CintegralIdentityAt n := by
  intro n hn
  by_cases h : n ≤ 28
  · exact cintegral_identity_le_twentyEight n h
  · interval_cases n
    · change L2chi3Real * (HA_coeff 29 : ℝ) - 2 * (HB_coeff 29 : ℝ) = cintegralJ 29
      exact CintegralIdentityAt_twentynine

/-- the instances of `CintegralIdentity` through `n = 30` -/
theorem cintegral_identity_le_thirty : ∀ n : ℕ, n ≤ 30 → CintegralIdentityAt n := by
  intro n hn
  by_cases h : n ≤ 29
  · exact cintegral_identity_le_twentyNine n h
  · interval_cases n
    · change L2chi3Real * (HA_coeff 30 : ℝ) - 2 * (HB_coeff 30 : ℝ) = cintegralJ 30
      exact CintegralIdentityAt_thirty

/-- the instances of `CintegralIdentity` through `n = 31` -/
theorem cintegral_identity_le_thirtyOne : ∀ n : ℕ, n ≤ 31 → CintegralIdentityAt n := by
  intro n hn
  by_cases h : n ≤ 30
  · exact cintegral_identity_le_thirty n h
  · interval_cases n
    · change L2chi3Real * (HA_coeff 31 : ℝ) - 2 * (HB_coeff 31 : ℝ) = cintegralJ 31
      exact CintegralIdentityAt_thirtyone

/-- the instances of `CintegralIdentity` through `n = 32` -/
theorem cintegral_identity_le_thirtyTwo : ∀ n : ℕ, n ≤ 32 → CintegralIdentityAt n := by
  intro n hn
  by_cases h : n ≤ 31
  · exact cintegral_identity_le_thirtyOne n h
  · interval_cases n
    · change L2chi3Real * (HA_coeff 32 : ℝ) - 2 * (HB_coeff 32 : ℝ) = cintegralJ 32
      exact CintegralIdentityAt_thirtytwo

/-- the instances of `CintegralIdentity` through `n = 33` -/
theorem cintegral_identity_le_thirtyThree : ∀ n : ℕ, n ≤ 33 → CintegralIdentityAt n := by
  intro n hn
  by_cases h : n ≤ 32
  · exact cintegral_identity_le_thirtyTwo n h
  · interval_cases n
    · change L2chi3Real * (HA_coeff 33 : ℝ) - 2 * (HB_coeff 33 : ℝ) = cintegralJ 33
      exact CintegralIdentityAt_thirtythree

/-- the instances of `CintegralIdentity` through `n = 34` -/
theorem cintegral_identity_le_thirtyFour : ∀ n : ℕ, n ≤ 34 → CintegralIdentityAt n := by
  intro n hn
  by_cases h : n ≤ 33
  · exact cintegral_identity_le_thirtyThree n h
  · interval_cases n
    · change L2chi3Real * (HA_coeff 34 : ℝ) - 2 * (HB_coeff 34 : ℝ) = cintegralJ 34
      exact CintegralIdentityAt_thirtyfour

/-- the instances of `CintegralIdentity` through `n = 35` -/
theorem cintegral_identity_le_thirtyFive : ∀ n : ℕ, n ≤ 35 → CintegralIdentityAt n := by
  intro n hn
  by_cases h : n ≤ 34
  · exact cintegral_identity_le_thirtyFour n h
  · interval_cases n
    · change L2chi3Real * (HA_coeff 35 : ℝ) - 2 * (HB_coeff 35 : ℝ) = cintegralJ 35
      exact CintegralIdentityAt_thirtyfive

/-!
## The parametric reduction of `CintegralIdentity` to the Zagier recurrence

The `(Cintegral)` coefficient identity relates two sequences that both
satisfy the **Zagier three-term P-recurrence**

`(n+1)²y_{n+1} = (10n² + 10n + 3)·yₙ − 9n²·y_{n−1}`   (`n ≥ 1`):

* the sequence `cₙ := L(2,χ₋₃)·aₙ − 2·bₙ` — because `(aₙ)` and `(bₙ)` do
  (`HA_coeff_recurrence`, `HB_coeff_recurrence`, both PROVED);
* the double integrals `Jₙ = cintegralJ n` — this is the one *analytic*
  input that is still open (the Beukers/Zagier evaluation of the period
  integrals, i.e. the (Cintegral)/Beukers-integral evaluation for general
  `n`).

Since a sequence satisfying that recurrence is determined by its first two
values, and the two base cases `n = 0, 1` are PROVED
(`CintegralIdentity_zero`, `cintegral_identity_one`), the *whole* of
`CintegralIdentity` — and hence the analytic conjunct of `EichlerInputB` —
follows from the single parametric recurrence for `J`.  The reductions below
record this precisely (`CintegralIdentity_of_recurrence`,
`overconvergesB_of_recurrence`). -/

/-- **the Zagier recurrence determines a sequence from its first two
values**: if `u`, `v` both satisfy
`(n+1)²y_{n+1} = (10n²+10n+3)yₙ − 9n²y_{n−1}` (`n ≥ 1`) and `u 0 = v 0`,
`u 1 = v 1`, then `u = v`. -/
theorem eq_of_zagier_recurrence {u v : ℕ → ℝ}
    (hu : ∀ n : ℕ, 1 ≤ n → ((n + 1 : ℕ) : ℝ) ^ 2 * u (n + 1)
      = (10 * (n : ℝ) ^ 2 + 10 * (n : ℝ) + 3) * u n - 9 * (n : ℝ) ^ 2 * u (n - 1))
    (hv : ∀ n : ℕ, 1 ≤ n → ((n + 1 : ℕ) : ℝ) ^ 2 * v (n + 1)
      = (10 * (n : ℝ) ^ 2 + 10 * (n : ℝ) + 3) * v n - 9 * (n : ℝ) ^ 2 * v (n - 1))
    (h0 : u 0 = v 0) (h1 : u 1 = v 1) : ∀ n, u n = v n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => exact h0
  | one => exact h1
  | more k ihk ihk1 =>
      have huk := hu (k + 1) (by omega)
      have hvk := hv (k + 1) (by omega)
      rw [show k + 1 + 1 = k + 2 by omega, show k + 1 - 1 = k by omega] at huk hvk
      have hne : (((k + 2 : ℕ)) : ℝ) ^ 2 ≠ 0 := by positivity
      apply mul_left_cancel₀ hne
      rw [huk, hvk, ihk, ihk1]

/-- the combination `L(2,χ₋₃)·aₙ − 2·bₙ` satisfies the Zagier recurrence
(from `HA_coeff_recurrence` and `HB_coeff_recurrence`) -/
theorem zagier_diff_recurrence (n : ℕ) (hn : 1 ≤ n) :
    ((n + 1 : ℕ) : ℝ) ^ 2
        * (L2chi3Real * (HA_coeff (n + 1) : ℝ) - 2 * (HB_coeff (n + 1) : ℝ))
      = (10 * (n : ℝ) ^ 2 + 10 * (n : ℝ) + 3)
          * (L2chi3Real * (HA_coeff n : ℝ) - 2 * (HB_coeff n : ℝ))
        - 9 * (n : ℝ) ^ 2
          * (L2chi3Real * (HA_coeff (n - 1) : ℝ) - 2 * (HB_coeff (n - 1) : ℝ)) := by
  have hA : ((n + 1 : ℕ) : ℝ) ^ 2 * (HA_coeff (n + 1) : ℝ)
      = (10 * (n : ℝ) ^ 2 + 10 * (n : ℝ) + 3) * (HA_coeff n : ℝ)
        - 9 * (n : ℝ) ^ 2 * (HA_coeff (n - 1) : ℝ) := by
    have h := HA_coeff_recurrence n hn
    exact_mod_cast h
  have hB : ((n + 1 : ℕ) : ℝ) ^ 2 * (HB_coeff (n + 1) : ℝ)
      = (10 * (n : ℝ) ^ 2 + 10 * (n : ℝ) + 3) * (HB_coeff n : ℝ)
        - 9 * (n : ℝ) ^ 2 * (HB_coeff (n - 1) : ℝ) := by
    have h := HB_coeff_recurrence n hn
    have h' : ((n + 1 : ℕ) : ℚ) ^ 2 * HB_coeff (n + 1)
        = ((10 : ℚ) * (n : ℚ) ^ 2 + 10 * (n : ℚ) + 3) * HB_coeff n
          - (9 : ℚ) * (n : ℚ) ^ 2 * HB_coeff (n - 1) := by
      linear_combination h
    exact_mod_cast h'
  linear_combination (L2chi3Real) * hA - 2 * hB

/-- **`CintegralIdentity` from the single parametric recurrence** for the
double integrals `Jₙ = cintegralJ n`. -/
theorem CintegralIdentity_of_recurrence
    (hrec : ∀ n : ℕ, 1 ≤ n → ((n + 1 : ℕ) : ℝ) ^ 2 * cintegralJ (n + 1)
      = (10 * (n : ℝ) ^ 2 + 10 * (n : ℝ) + 3) * cintegralJ n
        - 9 * (n : ℝ) ^ 2 * cintegralJ (n - 1)) : CintegralIdentity := by
  have h01 := eq_of_zagier_recurrence
    (u := fun n => L2chi3Real * (HA_coeff n : ℝ) - 2 * (HB_coeff n : ℝ))
    (v := cintegralJ) zagier_diff_recurrence hrec
    (by simpa [CintegralIdentityAt] using cintegral_identity_le_one 0 (by norm_num))
    (by simpa [CintegralIdentityAt] using cintegral_identity_le_one 1 (by norm_num))
  intro n
  exact h01 n

/-- **the analytic conjunct of `EichlerInputB` from the single parametric
recurrence**: `OverconvergesUnit eichlerDiffB` follows from the Zagier
recurrence for `cintegralJ`. -/
theorem overconvergesB_of_recurrence
    (hrec : ∀ n : ℕ, 1 ≤ n → ((n + 1 : ℕ) : ℝ) ^ 2 * cintegralJ (n + 1)
      = (10 * (n : ℝ) ^ 2 + 10 * (n : ℝ) + 3) * cintegralJ n
        - 9 * (n : ℝ) ^ 2 * cintegralJ (n - 1)) : OverconvergesUnit eichlerDiffB :=
  overconvergesB_of_cintegral (CintegralIdentity_of_recurrence hrec) cintegralJ_bound'

/-! ## The parametric recurrence is PROVED (commons lemma) — `(Cintegral)` closes

The commons lemma `Commons.Analysis.Integral.cintegral_recurrence_parametric`
(explicit divergence certificate `P(n,s,t) = P₀(s,t) + n·P₁(s,t)` for the
`(0,1)²`-integral of the `n`-family `9ⁿ(st)ⁿ(1−s³)ⁿ(1−t³)ⁿ/(1+st+s²t²)^{2n+1}`)
proves the Zagier recurrence for the double integrals for *all* `n ≥ 1`.
Through `CintegralIdentity_of_recurrence` this closes the whole
`(Cintegral)` identity, and hence the `H_B`-side overconvergence of node (2).
-/

/-- **the parametric Zagier recurrence** `(n+1)²J_{n+1} = (10n²+10n+3)Jₙ − 9n²J_{n−1}`
for the `(Cintegral)` double integrals, from the commons lemma
`Commons.Analysis.Integral.cintegral_recurrence_parametric` -/
theorem cintegralJ_recurrence : ∀ n : ℕ, 1 ≤ n →
    (((n + 1 : ℕ) : ℝ)) ^ 2 * cintegralJ (n + 1)
      = (10 * ((n : ℕ) : ℝ) ^ 2 + 10 * ((n : ℕ) : ℝ) + 3) * cintegralJ n
        - 9 * ((n : ℕ) : ℝ) ^ 2 * cintegralJ (n - 1) := by
  intro n hn
  have h := Commons.Analysis.Integral.cintegral_recurrence_parametric n hn
  simpa [cintegralJ, cintegralKernel] using h

/-- **`(Cintegral)` is PROVED**: `L(2,χ₋₃)·aₙ − 2·bₙ = Jₙ` for every `n` -/
theorem CintegralIdentity_proved : CintegralIdentity :=
  CintegralIdentity_of_recurrence cintegralJ_recurrence

/-- **the `H_B`-overconvergence of node (2), unconditional**:
`OverconvergesUnit eichlerDiffB` (radius-≥1 overconvergence of
`H_B − (L(2,χ₋₃)/2)·H_A`) -/
theorem overconvergesB_proved : OverconvergesUnit eichlerDiffB :=
  overconvergesB_of_cintegral CintegralIdentity_proved cintegralJ_bound'

/-- `EichlerInputB` from the modular conjunct and the parametric recurrence -/
theorem eichlerInputB_of_modular_and_recurrence (hMod : ModularIntegralityB)
    (hrec : ∀ n : ℕ, 1 ≤ n → ((n + 1 : ℕ) : ℝ) ^ 2 * cintegralJ (n + 1)
      = (10 * (n : ℝ) ^ 2 + 10 * (n : ℝ) + 3) * cintegralJ n
        - 9 * (n : ℝ) ^ 2 * cintegralJ (n - 1)) : EichlerInputB :=
  eichlerInputB_of_modular_and_cintegral hMod (CintegralIdentity_of_recurrence hrec)
    cintegralJ_bound'

/-- **`EichlerInputB` from the modular conjunct alone**: the analytic
(overconvergence) half is now proved; only the modular `[1..n]²`-integrality
remains. -/
theorem eichlerInputB_of_modular (hMod : ModularIntegralityB) : EichlerInputB :=
  eichlerInputB_of_modular_and_recurrence hMod cintegralJ_recurrence

end Submission.CDT
