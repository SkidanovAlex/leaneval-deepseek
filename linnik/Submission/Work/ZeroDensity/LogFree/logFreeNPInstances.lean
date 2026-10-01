import Mathlib
import Submission.Work.ZeroDensity.LogFree.logFreeNPOfParams
import Submission.Work.ZeroDensity.LogFree.nonPrincipalTwelveFifths
import Submission.Work.LinnikAreas.FarBoundOfJutilaMontgomery
import Submission.Work.ZeroFreeTables.OtherLamCountBounded_of_logFreeNP

/-!
# `Work.ZeroDensity.LogFree.logFreeNPInstances` — the two instances of the unified estimate, and
the bridges to the consumers

The lead's table (`JUTILA_UNIFIED_LEAD.md` §3) specifies two parameter packets of the unified
log-free estimate `logFreeNP`:

* **instance I** (`σ₀ = 3979/5000 = 1 - 1021/5000`, `η = 1/100`, `w = 1/100`, `u = 47/50`,
  `v = 99/100`, `x = 49/25`), giving `2x = 3.92 ≤ 4`: this is the packet of Areas 2 and 3, and it
  yields `Work.ZeroDensity.LogFree.logFreeNP (3979/5000) 4`, hence the consumer statement
  `Work.LinnikAreas.FamilyZeroDensityJutilaCrudeWide`;
* **instance II** (`σ₀ = 93/100`, `η = 1/1000`, `w = 1/1000`, `u = 59/100`, `v = 119/200`,
  `x = 237/200`), giving `2x = 2.37 ≤ 12/5`: this is the near-line packet of Area 6, and it yields
  `logFreeNP (93/100) (12/5)`, hence (glued with Huxley's widened `12/5` estimate) Heath-Brown's
  (1.4) for the non-principal characters, `NonPrincipalTwelveFifths`.

Both instances are **unconditional**: `Work.ZeroDensity.LogFree.logFreeNPOfParams` proves, for every
parameter packet `p`, `Σ'_{χ ≠ 1} N(σ,T,χ) ≤ C (qT)^{2·p.x·(1-σ)}` — the Halász duality count
`DualityCount p` is discharged by `Work.ZeroDensity.LogFree.dualityCountOfParamsCF` from the eight
axiom-clean interfaces of `LogFree/GramProps.lean` (through the clash-free mirror copies of
`Work/HB7CF2/`), and the box upgrade is the unconditional `LogFree/boxUpgradeOfParams`.  The bridges
to `FamilyZeroDensityJutilaCrudeWide` (Area 2) and to `OtherLamCountBounded` (Areas 3 and 6)
therefore need no hypothesis either.
-/

open DirichletCharacter
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroDensity.LogFree

/-- **Parameter packet I** of `JUTILA_UNIFIED_LEAD.md` §3 (`σ₀ = 3979/5000`, `2x = 3.92`). -/
def paramsI : Params where
  σ₀ := 3979 / 5000
  η := 1 / 100
  w := 1 / 100
  u := 47 / 50
  v := 99 / 100
  x := 49 / 25
  hσ₀ := by norm_num
  hσ₀1 := by norm_num
  hη := by norm_num
  hw := by norm_num
  hwu := by norm_num
  huv := by norm_num
  hvx := by norm_num
  P1 := by norm_num
  P2 := by norm_num

/-- **Parameter packet II** of `JUTILA_UNIFIED_LEAD.md` §3 (`σ₀ = 93/100`, `2x = 2.37`). -/
def paramsII : Params where
  σ₀ := 93 / 100
  η := 1 / 1000
  w := 1 / 1000
  u := 59 / 100
  v := 119 / 200
  x := 237 / 200
  hσ₀ := by norm_num
  hσ₀1 := by norm_num
  hη := by norm_num
  hw := by norm_num
  hwu := by norm_num
  huv := by norm_num
  hvx := by norm_num
  P1 := by norm_num
  P2 := by norm_num

/-- **Instance I**: `logFreeNP (3979/5000) 4` (`2x = 3.92 < 4`).  Unconditional. -/
theorem logFreeNP_3979_5000_four : logFreeNP (3979 / 5000) 4 := by
  obtain ⟨C, hC, hh⟩ := logFreeNPOfParams paramsI
  refine ⟨C, hC, ?_⟩
  intro q hq _inst σ T hσ hσ1 hT
  have hσ' : paramsI.σ₀ ≤ σ := by simpa only [paramsI] using hσ
  have hbase : (1 : ℝ) ≤ (q : ℝ) * T := by
    have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith
  have hexp : 2 * paramsI.x * (1 - σ) ≤ 4 * (1 - σ) := by
    have h0 : (0 : ℝ) ≤ 1 - σ := by linarith
    have hx : 2 * paramsI.x ≤ 4 := by norm_num [paramsI]
    nlinarith
  refine le_trans (hh q hq σ T hσ' hσ1 hT) ?_
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC)
  exact Real.rpow_le_rpow_of_exponent_le hbase hexp

/-- **Instance II**: `logFreeNP (93/100) (12/5)` (`2x = 2.37 < 12/5`).  Unconditional. -/
theorem logFreeNP_93_100_twelveFifths : logFreeNP (93 / 100) (12 / 5) := by
  obtain ⟨C, hC, hh⟩ := logFreeNPOfParams paramsII
  refine ⟨C, hC, ?_⟩
  intro q hq _inst σ T hσ hσ1 hT
  have hσ' : paramsII.σ₀ ≤ σ := by simpa only [paramsII] using hσ
  have hbase : (1 : ℝ) ≤ (q : ℝ) * T := by
    have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith
  have hexp : 2 * paramsII.x * (1 - σ) ≤ (12 / 5) * (1 - σ) := by
    have h0 : (0 : ℝ) ≤ 1 - σ := by linarith
    have hx : 2 * paramsII.x ≤ 12 / 5 := by norm_num [paramsII]
    nlinarith
  refine le_trans (hh q hq σ T hσ' hσ1 hT) ?_
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC)
  exact Real.rpow_le_rpow_of_exponent_le hbase hexp

/-! ## The bridges to the consumers -/

/-- **Area 2**: the log-free estimate `logFreeNP (3979/5000) 4` implies the crude wide-range
family estimate `Work.LinnikAreas.FamilyZeroDensityJutilaCrudeWide`
(`Σ_{χ ≠ 1} N(σ,T,χ) ≤ C (qT)^{(24/5+ε)(1-σ)}` on `σ ≥ 3979/5000`), because
`4 ≤ 24/5 + ε`. -/
theorem familyZeroDensityJutilaCrudeWide_of_logFreeNP
    (h : logFreeNP (3979 / 5000) 4) :
    Work.LinnikAreas.FamilyZeroDensityJutilaCrudeWide := by
  intro ε hε
  obtain ⟨C, hC, hh⟩ := h
  refine ⟨C, hC, ?_⟩
  intro q hq _inst σ T hσ hσ1 hT
  have hbase : (1 : ℝ) ≤ (q : ℝ) * T := by
    have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith
  have hexp : 4 * (1 - σ) ≤ ((24 : ℝ) / 5 + ε) * (1 - σ) := by
    have h0 : (0 : ℝ) ≤ 1 - σ := by linarith
    nlinarith [hε, h0]
  have hσ' : (3979 / 5000 : ℝ) ≤ σ := by
    have heq : (3979 / 5000 : ℝ) = 1 - 1021 / 5000 := by norm_num
    rw [heq]; exact hσ
  have hmain := hh q hq σ T hσ' hσ1 hT
  have hmain' : (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      Work.LinnikAreas.zeroCountIn χ σ T) ≤ C * ((q : ℝ) * T) ^ (4 * (1 - σ)) := by
    simpa only [famCountNP, zCount] using hmain
  exact le_trans hmain' (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hbase hexp) (le_of_lt hC))

/-- **Area 2 (unconditional)**: the crude wide-range family estimate
`Work.LinnikAreas.FamilyZeroDensityJutilaCrudeWide`, from instance I. -/
theorem familyZeroDensityJutilaCrudeWide :
    Work.LinnikAreas.FamilyZeroDensityJutilaCrudeWide :=
  familyZeroDensityJutilaCrudeWide_of_logFreeNP logFreeNP_3979_5000_four

/-- **Areas 3 and 6 (unconditional)**: Heath-Brown's Lemma 6.1 (`Table 7`'s only analytic input)
from instance I.  `Work.ZeroFreeTables.OtherLamCountBounded` is the multiplicity-weighted count of
the zeros of the characters `χ ∉ {1, χ₁, χ₁⁻¹}` with `λ(ρ) ≤ Λ ≤ 3` and `|Im ρ| ≤ H`, bounded by a
constant uniform in `q` and in `χ₁`; `OtherLamCountBounded_of_logFreeNP` produces it from any
`(c+ε)`-form log-free non-principal estimate, and instance I has `c = 4`. -/
theorem otherLamCountBounded : Work.ZeroFreeTables.OtherLamCountBounded := by
  refine Work.ZeroFreeTables.OtherLamCountBounded_of_logFreeNP (3979 / 5000) 4
    (by norm_num) (by norm_num) ?_
  intro ε hε
  obtain ⟨C, hC, hh⟩ := logFreeNP_3979_5000_four
  refine ⟨C, hC, ?_⟩
  intro q hq _inst σ T hσ hσ1 hT
  have hbase : (1 : ℝ) ≤ (q : ℝ) * T := by
    have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith
  refine le_trans (hh q hq σ T hσ hσ1 hT) ?_
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC)
  refine Real.rpow_le_rpow_of_exponent_le hbase ?_
  have h0 : (0 : ℝ) ≤ 1 - σ := by linarith
  nlinarith [hε, h0]

/-- **Area 6**: Heath-Brown's (1.4) for the non-principal characters, from instance II and the
widened Huxley estimate `HuxleyNPWide` (see `LogFree/huxleyNPWideOfHalves.lean` for its proof from
the two halves of Montgomery's detector). -/
theorem nonPrincipalTwelveFifths_of_huxley (hhux : HuxleyNPWide) :
    NonPrincipalTwelveFifths :=
  nonPrincipalTwelveFifths logFreeNP_93_100_twelveFifths hhux

end Work.ZeroDensity.LogFree
