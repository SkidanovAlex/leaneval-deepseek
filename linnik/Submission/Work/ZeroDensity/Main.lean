import Mathlib
import Submission.Work.ZeroDensity.Basic
import Submission.Work.LinnikAreas.FamilyZeroDensitySplitting
import Submission.Work.LinnikAreas.FarBoundOfJutilaMontgomery
import Submission.Work.ZeroDensity.Deuring.deuringHeilbronnLogFree
import Submission.Work.ZeroDensity.Assembly.logFreeFamHeight_of_cores
import Submission.Work.ZeroDensity.Counts.famCount_mono

/-!
# `Work.ZeroDensity.Main` — the assembly, and the exact state of the three deliverables

This module is the *interface* of the chapter: it assembles the consumer-facing `Prop`s of the
Areas from the chapter's density statements, and it records, as `Prop`-valued structures, exactly
which deep cores remain.

## The three deliverables and their cores

**(D1) the log-free density near `σ = 1`** (Heath-Brown §11's zero detector with `k` fixed, i.e.
`φ = 1/2` by convexity, `c = 4φ + ε = 2 + ε < 4`), for `(1-σ)𝓛 ≤ A log 𝓛`:

* `NearLineLogFree c A` — the `Prop` (Defs), target
  `Work.ZeroDensity.NearLine.nearLineLogFree : NearLineLogFree 2 (1/3)`.
* the *full-range* log-free form on `σ ≥ 4/5`, which is what the consumer
  `Work.LinnikAreas.FamilyZeroDensityJutila` actually needs, is
  `FamDensityEpsRange (4/5) 1 2` (target `Work.ZeroDensity.Jutila.jutilaLogFree`).

**(D2) Montgomery's density theorem** (multiplicative large sieve),
`Σ_χ N(σ,T,χ) ≪ (qT)^{3(1-σ)/(2-σ)}(log qT)^B`:

* `MontgomerySharp B` — the `Prop` (Defs), target
  `Work.ZeroDensity.Montgomery.montgomerySharp : ∀ B > 0, MontgomerySharp B`.
* `montgomerySharp_to_powerRange` (proved below, in `Basic`) converts it, together with the
  σ-blind count, into the `12/5`-exponent statement on `σ ≤ 3/4`; the remaining range
  `3/4 < σ ≤ 4/5` is Huxley's `12/5` estimate, `FamDensityEpsRange 0 (4/5) (12/5)`
  (target `Work.ZeroDensity.Huxley.huxleyTwelveFifths`), which gives the consumer
  `Work.LinnikAreas.FamilyZeroDensityMontgomery`.

**(D3) the log-free Deuring–Heilbronn density bound with the `λ₁` factor** (Bombieri, *Le grand
crible*, Thm. 14; Jutila 1977), covering `χ₀`:

* `DHLogFree c` (working region `|Im ρ| ≤ 1`) — target
  `Work.ZeroDensity.Deuring.deuringHeilbronnLogFree`, where the case `|Im ρ| ≤ 1` is *reduced* to
  `LogFreeFamHalf (5/2)` (a log-free family count at height `1`) plus the explicit-constant
  Deuring–Heilbronn repulsion `RepulsionWith (7/16)`; the assembly `c = 5/2 + 16/7 = 67/14 < 49/10`
  is the two-exponential matching of `Work.LinnikAreas.ownCount_le_of_threshold_and_logfree`.
* `DHLogFreeHeight c c'` (full height range) — target
  `Work.ZeroDensity.Deuring.deuringHeilbronnHeight`.
* `Work.ZeroDensity.pairDensityInput_of_dhLogFreeSpec` and
  `Work.ZeroDensity.pairDensityHeightInput_of_dhLogFreeHeightSpec` (proved in `Basic`) turn these
  into the two Area 6 inputs `Work.LinnikAreas.Siegel.PairDensityInput` and
  `PairDensityHeightInput`.

## What is proved unconditionally here

`famDensityPowerRange_half` (`σ ≤ 1/2`, exponent `12/5`), `trivial_bound`,
`trivial_famDensityPowerRange`, `montgomerySharp_to_powerRange`, `famDensityEpsRange_glue`,
`logFreeFamHalf_of_density` and all the bridges of `Basic.lean`.  The three cores (D1), (D2), (D3)
are stated as `Prop`s in `Defs.lean` and delegated.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroDensity

open Work.LinnikContract

/-! ## 1. The cores, as a single structure -/

/-- **The deep cores of this chapter.**  Everything the consumers need follows from these five
`Prop`s by the proved assemblies below; each of them is a named classical theorem of the
literature (see the module docstring). -/
structure DensityCores : Prop where
  /-- Jutila's log-free family zero count on `σ ≥ 4/5`. -/
  jutila : FamDensityEpsRange (4/5) 1 2
  /-- Huxley's `12/5` family zero count on `σ ≤ 4/5`. -/
  huxley : FamDensityEpsRange 0 (4/5) (12/5)
  /-- Montgomery's sharp large-sieve density estimate. -/
  montgomery : ∀ B : ℝ, 0 < B → MontgomerySharp B
  /-- The Deuring–Heilbronn repulsion with the explicit constant `7/16`. -/
  repulsion : RepulsionWith (7/16)
  /-- The `λ₁`-saving log-free Deuring–Heilbronn count in both variables. -/
  dhHeight : DHLogFreeHeightSpec

/-! ## 2. Unconditional content -/

/-- **The `12/5` bound on `σ ≤ 1/2` is a theorem of this chapter** (the σ-blind count of the
workspace): there, `(12/5)(1-σ) ≥ 6/5 > 1`. -/
theorem famDensityPowerRange_half {B : ℝ} (hB : 0 ≤ B) :
    FamDensityPowerRange 0 (1/2) (12/5) B :=
  trivial_famDensityPowerRange (σlo := 0) (σhi := 1/2) (c := 12/5) (B := B)
    (by norm_num) le_rfl (by norm_num) hB (by norm_num)

/-! ## 3. The assemblies -/

/-- **The log-free count at height `1` with exponent `5/2`**, from Jutila's `σ ≥ 4/5` estimate and
Huxley's `12/5` estimate on `σ ≤ 4/5` (glued, with `max (12/5) 2 = 12/5`, and `12/5 + 1/10 = 5/2`). -/
theorem logFreeFamHalf_two_half (hJ : FamDensityEpsRange (4/5) 1 2)
    (hH : FamDensityEpsRange 0 (4/5) (12/5)) : LogFreeFamHalf (5/2) := by
  have hglue : FamDensityEpsRange 0 1 (12/5) := by
    have h := famDensityEpsRange_glue (σlo := 0) (m := 4/5) (σhi := 1)
      (c := 12/5) (c' := 2) hH hJ
    have hmax : max (12/5 : ℝ) 2 = 12/5 := by norm_num [max_def]
    rwa [hmax] at h
  have h2 : LogFreeFamHalf ((12:ℝ)/5 + 1/10) := logFreeFamHalf_of_density (by norm_num) hglue
  have heq : ((12:ℝ)/5 + 1/10) = 5/2 := by norm_num
  rwa [heq] at h2

/-- **Jutila's estimate is the Area 2 input** `Work.LinnikAreas.FamilyZeroDensityJutila`. -/
theorem familyZeroDensityJutila_of_core (hJ : FamDensityEpsRange (4/5) 1 2) :
    Work.LinnikAreas.FamilyZeroDensityJutila :=
  familyZeroDensityJutila_of_famDensityEpsRange hJ

/-- **Huxley's estimate is the Area 2 input** `Work.LinnikAreas.FamilyZeroDensityMontgomery`
(through the workspace's already proved `FamilyZeroDensityMontgomery_of_huxley`, or directly
through the glued `FamDensityEpsRange 0 1 (12/5)`). -/
theorem familyZeroDensityMontgomery_of_cores (hJ : FamDensityEpsRange (4/5) 1 2)
    (hH : FamDensityEpsRange 0 (4/5) (12/5)) : Work.LinnikAreas.FamilyZeroDensityMontgomery := by
  have hglue : FamDensityEpsRange 0 1 (12/5) := by
    have h := famDensityEpsRange_glue (σlo := 0) (m := 4/5) (σhi := 1)
      (c := 12/5) (c' := 2) hH hJ
    have hmax : max (12/5 : ℝ) 2 = 12/5 := by norm_num [max_def]
    rwa [hmax] at h
  have hpow : FamDensityPowerForm 0 (4/5) (12/5) := fun B hB =>
    famDensityPowerRange_mono (σlo := 0) (σhi := 1) (c := 12/5)
      (σlo' := 0) (σhi' := 4/5) (c' := 12/5) le_rfl (by norm_num) le_rfl
      (hglue.toFamDensityPowerRange hB.le)
  exact familyZeroDensityMontgomery_of_powerForm hpow

/-- **The Deuring–Heilbronn working-region bound, from the two density cores and the repulsion with
the explicit constant `7/16`.**  This is the proved reduction
`Work.ZeroDensity.Deuring.deuringHeilbronnLogFree` applied to the height-`1` counting bound
`logFreeFamHalf_two_half`. -/
theorem deuringLogFree_of_cores (hJ : FamDensityEpsRange (4/5) 1 2)
    (hH : FamDensityEpsRange 0 (4/5) (12/5)) (hrep : RepulsionWith (7/16)) : DHLogFreeSpec :=
  Deuring.deuringHeilbronnLogFree (logFreeFamHalf_two_half hJ hH) hrep

/-- **The Area 6 input `PairDensityInput`, from the two density cores and the repulsion.** -/
theorem pairDensityInput_of_cores (hJ : FamDensityEpsRange (4/5) 1 2)
    (hH : FamDensityEpsRange 0 (4/5) (12/5)) (hrep : RepulsionWith (7/16)) :
    Work.LinnikAreas.Siegel.PairDensityInput :=
  pairDensityInput_of_dhLogFreeSpec (deuringLogFree_of_cores hJ hH hrep)

/-- **Heath-Brown's (1.4) / the `FamilyZeroDensityHyp` of Area 2**, from the two cores (Jutila on
`σ ≥ 4/5`, Huxley on `σ ≤ 4/5`): the glued `FamDensityEpsRange 0 1 (12/5)` *is*
`Work.LinnikAreas.FamilyZeroDensityHyp`. -/
theorem familyZeroDensityHyp_of_cores (hJ : FamDensityEpsRange (4/5) 1 2)
    (hH : FamDensityEpsRange 0 (4/5) (12/5)) : Work.LinnikAreas.FamilyZeroDensityHyp := by
  intro ε hε
  obtain ⟨C, hC, hh⟩ := hJ ε hε
  obtain ⟨C', hC', hh'⟩ := hH ε hε
  refine ⟨max C C', lt_max_of_lt_left hC, ?_⟩
  intro q hq _inst σ T h0 hσ1 hT
  have hbase : (1 : ℝ) ≤ (q : ℝ) * T := one_le_base hq hT
  have hpow : (0 : ℝ) ≤ ((q : ℝ) * T) ^ ((12/5 + ε) * (1 - σ)) :=
    Real.rpow_nonneg (rpow_base_nonneg hq hT) _
  rcases le_total σ (4/5 : ℝ) with h | h
  · refine le_trans (hh' q hq σ T h0 h hT) ?_
    exact mul_le_mul_of_nonneg_right (le_max_right C C') hpow
  · have hexp : ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ))
        ≤ ((q : ℝ) * T) ^ ((12/5 + ε) * (1 - σ)) := by
      refine Real.rpow_le_rpow_of_exponent_le hbase ?_
      have h1 : (0 : ℝ) ≤ 1 - σ := by linarith
      nlinarith
    refine le_trans (hh q hq σ T h hσ1 hT) ?_
    refine le_trans (mul_le_mul_of_nonneg_left hexp (le_of_lt hC)) ?_
    exact mul_le_mul_of_nonneg_right (le_max_left C C') hpow

theorem pairDensityHeightInput_of_core (h : DHLogFreeHeightSpec) :
    Work.LinnikAreas.Siegel.PairDensityHeightInput :=
  pairDensityHeightInput_of_dhLogFreeHeightSpec h

/-! ## 4. Re-exported assemblies from the branch modules -/

/-- **The separated-exponent log-free height count `5/2, 3/2` from the two cores** — the proved
assembly `Work.ZeroDensity.Assembly.logFreeFamHeight_of_cores`. -/
theorem logFreeFamHeight_two_half (hJ : FamDensityEpsRange (4/5) 1 2)
    (hH : FamDensityEpsRange 0 (4/5) (12/5)) : LogFreeFamHeight (5/2) (3/2) :=
  Assembly.logFreeFamHeight_of_cores hJ hH

end Work.ZeroDensity
