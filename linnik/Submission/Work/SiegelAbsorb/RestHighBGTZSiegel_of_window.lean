import Mathlib
import Submission.Work.SiegelAbsorb.windowInterface
import Submission.Work.SiegelAbsorb.famCount_nearLine
import Submission.Work.SiegelAbsorb.famCountCrudeCorollaries
import Submission.Work.SiegelAbsorb.lamOf_ge_exp_neg
import Submission.Work.LinnikAreas.RestHighFree
import Submission.Work.LinnikAreas.BGTZZFR
import Submission.Work.LinnikAreas.BGTZ.AuxC

/-!
# `Work.SiegelAbsorb.RestHighBGTZSiegel_of_window`

This is the *second half* of the Siegel-absorption route of AREA 6 (see
`Submission/Work/SiegelAbsorb/windowInterface.lean`): it turns the two-regime per-window mass bound
`WindowBoundHyp` (proved, uniformly in its three constants, by `Work.SiegelAbsorb.highMassRep2`)
together with the Deuring--Heilbronn repulsion `RepulsionGenC (11/5) (11/10) C₀` and the
zero-free region `ZFRInput cZ` into the `λ₁`-saving high-zero bound
`Siegel.RestHighBGTZSpec (-3/2)`.

The proof is that of `Work.LinnikAreas.BGTZ.RestHighBGTZGenC` with the single family count
`LogFreeFamHeight (5/2) (3/2)` replaced by the two counts that AREA 6 actually has
(`Work.SiegelAbsorb.famCount_nearLine` at coefficient `5/2` on the near line and
`Work.SiegelAbsorb.famCount_crude` at coefficient `9/2` everywhere), and with the `λ₁`-saving
window bound `highMassRepC` replaced by the hypothesis `WindowBoundHyp`:

* the family count of coefficient `5/2` is fed to `WindowBoundHyp` (its `hfam₁`);
* the crude count of coefficient `9/2` is fed to `WindowBoundHyp` (its `hfam₂`) and, through
  `Work.LinnikAreas.high_finset_bound_hi` at `c = 9/2` (lemma `crudeFreeFinsetBound` below), also
  supplies the `λ₁`-free branch `σ ≤ λ₁`;
* the summand `K₃high C₃ · e^{-(7/250)𝓛}` of the window bound is absorbed into
  `K₃high C₃ · λ₁` by Siegel's bound `λ₁ ≥ e^{-(7/250)𝓛}`
  (`Work.SiegelAbsorb.lamOf_ge_exp_neg`);

everything else — Siegel's lower bounds for `λ₁`, the split point `σ`, the height threshold
`e^{20+1/Csi+1/√Cₛ}`, the zero-free-region height separation
`Work.LinnikAreas.BGTZ.height_sep_of_ZFR`, the passage from finite-set bounds to the series
`Siegel.restHighZeroSum` (lemma `restHighZeroSumFinset` below) and the final `𝓛^{-2} → 𝓛^{-3/2}`
step — is copied from `Work.LinnikAreas.BGTZ.RestHighBGTZGenC`.
-/

namespace Work.SiegelAbsorb

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section
open Work.LinnikContract

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- **The `λ₁`-free per-fibre mass bound at the crude coefficient `9/2`.**

With a family count `famCount q σ T ≤ Cc·e^{(9/2)(1-σ)𝓛}·T^{3/2}` valid on all of `[0,1]` (the
crude count `Work.SiegelAbsorb.famCount_crude`), the multiplicity-weighted kernel sum over any
finite set of *high* zero-pairs (excluding the exceptional pair `(χ₁,β₁)`) is at most
`4·Cc·D·B·𝓛^{-2}`, `D = e^{max(9/2)0}(1-e^{max(9/2)0-49/10})⁻¹`,
`B = 2^{3/2}(1-2^{3/2-2})⁻¹`.

This is `Work.LinnikAreas.high_finset_bound_hi` at `c = 9/2`, `c' = 3/2`, `lam1 = 𝓛^{-3/2}`,
whose counting hypothesis comes from `Work.LinnikAreas.pairCountHeight_le_famCount_scaled`; it is
the `λ₁`-free branch of the main theorem below. -/
private theorem crudeFreeFinsetBound {q : ℕ} [NeZero q] (hq : 1 < q)
    (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ) {Cc : ℝ} (hCc : 0 < Cc)
    (hfam : ∀ σ T : ℝ, 0 ≤ σ → σ ≤ 1 → 1 ≤ T →
      Work.ZeroDensity.famCount q σ T
        ≤ Cc * Real.exp ((9 / 2) * ((1 - σ) * Real.log (q : ℝ))) * T ^ (3 / 2 : ℝ))
    (S : Finset (DirichletCharacter ℂ q × ℂ))
    (hzm : ∀ z ∈ S, zeroMult z.1 z.2 ≠ 0)
    (hhigh : ∀ z ∈ S, 1 < |z.2.im|)
    (hexc : ∀ z ∈ S, ¬(z.1 = χ₁ ∧ z.2 = β₁)) :
    (∑ z ∈ S, (zeroMult z.1 z.2 : ℝ)
        * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
      ≤ 4 * Cc * (Real.exp (max (9 / 2) 0) * (1 - Real.exp (max (9 / 2) 0 - 49 / 10))⁻¹)
          * ((2 : ℝ) ^ (3 / 2 : ℝ) * (1 - (2 : ℝ) ^ ((3 / 2 : ℝ) - 2))⁻¹)
          * (Real.log q) ^ (-2 : ℝ) := by
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq)
  have hcnt : ∀ t T : ℝ, 0 < t → t ≤ Real.log (q : ℝ) → Real.log (q : ℝ) ≤ T →
      Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t T
        ≤ Cc * (Real.log (q : ℝ)) ^ (-(3 / 2) : ℝ) * Real.exp ((9 / 2) * t)
            * T ^ (3 / 2 : ℝ) := by
    intro t T ht htL hT
    exact Work.LinnikAreas.pairCountHeight_le_famCount_scaled (q := q) hq χ₁ β₁
      (C := Cc) (c := 9 / 2) (c' := 3 / 2) hfam ht htL hT
  have hmain := Work.LinnikAreas.high_finset_bound_hi (q := q) hq χ₁ β₁
    (C := Cc) (c := 9 / 2) (c' := 3 / 2) (lam1 := (Real.log (q : ℝ)) ^ (-(3 / 2) : ℝ))
    hCc (Real.rpow_pos_of_pos hlog _) (by norm_num) (by norm_num) hcnt S hzm hhigh hexc
  have hsplit : (Real.log (q : ℝ)) ^ (-(3 / 2) : ℝ)
      * (Real.log (q : ℝ)) ^ ((3 / 2 : ℝ) - 2) = (Real.log (q : ℝ)) ^ (-2 : ℝ) := by
    rw [← Real.rpow_add hlog]
    norm_num
  refine le_trans hmain (le_of_eq ?_)
  calc 4 * Cc * (Real.log (q : ℝ)) ^ (-(3 / 2) : ℝ)
        * (Real.exp (max (9 / 2) 0) * (1 - Real.exp (max (9 / 2) 0 - 49 / 10))⁻¹)
        * ((2 : ℝ) ^ (3 / 2 : ℝ) * (1 - (2 : ℝ) ^ ((3 / 2 : ℝ) - 2))⁻¹)
        * (Real.log (q : ℝ)) ^ ((3 / 2 : ℝ) - 2)
      = 4 * Cc
        * (Real.exp (max (9 / 2) 0) * (1 - Real.exp (max (9 / 2) 0 - 49 / 10))⁻¹)
        * ((2 : ℝ) ^ (3 / 2 : ℝ) * (1 - (2 : ℝ) ^ ((3 / 2 : ℝ) - 2))⁻¹)
        * ((Real.log (q : ℝ)) ^ (-(3 / 2) : ℝ)
            * (Real.log (q : ℝ)) ^ ((3 / 2 : ℝ) - 2)) := by ring
    _ = 4 * Cc
        * (Real.exp (max (9 / 2) 0) * (1 - Real.exp (max (9 / 2) 0 - 49 / 10))⁻¹)
        * ((2 : ℝ) ^ (3 / 2 : ℝ) * (1 - (2 : ℝ) ^ ((3 / 2 : ℝ) - 2))⁻¹)
        * (Real.log (q : ℝ)) ^ (-2 : ℝ) := by rw [hsplit]

/-- **Finite-set bounds give the series bound.**  If every finite partial sum of the (nonnegative)
integrand of `Siegel.restHighZeroSum χ₁ β₁ (11/2) (3/10)` is at most `C`, then the series itself is
at most `C`.  This packages the `summable_of_sum_le` + `Real.tsum_le_of_sum_le` +
`Summable.tsum_prod` + `tsum_fintype` step that closes the proofs of
`Work.LinnikAreas.RestHighFree` and `Work.LinnikAreas.BGTZ.RestHighBGTZGenC`. -/
private theorem restHighZeroSumFinset {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ)
    {C : ℝ}
    (hbound : ∀ u : Finset (DirichletCharacter ℂ q × ℂ),
      (∑ z ∈ u, (if zeroMult z.1 z.2 ≠ 0 ∧ 1 < |z.2.im| ∧
            ¬(z.1 = χ₁ ∧ z.2 = β₁)
          then (zeroMult z.1 z.2 : ℝ)
            * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖
          else 0)) ≤ C) :
    Work.LinnikAreas.Siegel.restHighZeroSum χ₁ β₁ (11 / 2) (3 / 10) ≤ C := by
  classical
  let F : DirichletCharacter ℂ q × ℂ → ℝ := fun z =>
    if zeroMult z.1 z.2 ≠ 0 ∧ 1 < |z.2.im| ∧ ¬(z.1 = χ₁ ∧ z.2 = β₁)
    then (zeroMult z.1 z.2 : ℝ)
      * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖
    else 0
  have hFnn : 0 ≤ F := fun z => by
    simp only [F]
    split_ifs with hp
    · exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
    · exact le_refl 0
  have hb : ∀ u : Finset (DirichletCharacter ℂ q × ℂ), ∑ z ∈ u, F z ≤ C := fun u => by
    simpa only [F] using hbound u
  have hsumm : Summable F := summable_of_sum_le hFnn hb
  have htsum : ∑' z : DirichletCharacter ℂ q × ℂ, F z ≤ C :=
    Real.tsum_le_of_sum_le hFnn hb
  rw [Summable.tsum_prod hsumm] at htsum
  rw [tsum_fintype] at htsum
  have hEq : Work.LinnikAreas.Siegel.restHighZeroSum χ₁ β₁ (11 / 2) (3 / 10)
      = ∑ χ : DirichletCharacter ℂ q, ∑' ρ : ℂ, F (χ, ρ) := rfl
  rw [hEq]
  exact htsum

theorem RestHighBGTZSiegel_of_window
    (hw : ∀ (C₂ C₃ C₀ : ℝ), 0 < C₂ → 0 < C₃ → 0 < C₀ →
      Work.SiegelAbsorb.WindowBoundHyp C₂ C₃ C₀)
    (cZ C₀ : ℝ) (hcZ : 0 < cZ) (hC₀ : 0 < C₀)
    (hrep : Work.LinnikAreas.BGTZ.RepulsionGenC (11 / 5) (11 / 10) C₀)
    (hzfr : Work.LinnikAreas.BGTZ.ZFRInput cZ) :
    Work.LinnikAreas.Siegel.RestHighBGTZSpec (-3 / 2) := by
  classical
  -- the two family counts, Siegel's two lower bounds for `λ₁`, the repulsion, the ZFR and the
  -- exponential lower bound for `λ₁`
  obtain ⟨Cn, hCnpos, hnear⟩ := famCount_nearLine
  obtain ⟨Cc, hCcpos, hcrude⟩ := famCount_crude
  obtain ⟨Cₛ, hCₛpos, hCₛ⟩ := Work.LinnikAreas.lamOfEps200
  obtain ⟨Csi, hCsipos, hCsi⟩ := Work.LinnikAreas.Siegel.lamOf_lower_bound
  obtain ⟨q₀rep, hrepall⟩ := hrep
  obtain ⟨q₀zfr, hzfrall⟩ := hzfr
  obtain ⟨q₀exp, hexpall⟩ := lamOf_ge_exp_neg (a := 7 / 250) (by norm_num)
  -- the split point of the two regimes
  set σ : ℝ := min (1 / 10) (min (cZ / 4) (1 / (6 * C₀))) with hσdef
  have hσpos : 0 < σ := by
    rw [hσdef]
    exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hσ10 : σ ≤ 1 / 10 := by rw [hσdef]; exact min_le_left _ _
  have hσcZ : σ ≤ cZ / 4 := by
    rw [hσdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hσC₀ : σ ≤ 1 / (6 * C₀) := by
    rw [hσdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  -- the constant of the `λ₁`-free branch
  set Kf : ℝ := 4 * Cc * (Real.exp (max (9 / 2) 0) * (1 - Real.exp (max (9 / 2) 0 - 49 / 10))⁻¹)
      * ((2 : ℝ) ^ (3 / 2 : ℝ) * (1 - (2 : ℝ) ^ ((3 / 2 : ℝ) - 2))⁻¹) with hKfdef
  have hKfpos : 0 < Kf := by
    rw [hKfdef]
    have h1 : Real.exp (max (9 / 2 : ℝ) 0 - 49 / 10) < 1 := by
      rw [Real.exp_lt_one_iff]
      have h2 : max (9 / 2 : ℝ) 0 = 9 / 2 := max_eq_left (by norm_num)
      rw [h2]; norm_num
    have h2 : (2 : ℝ) ^ ((3 / 2 : ℝ) - 2) < 1 := by
      have h3 : 1 < (2 : ℝ) ^ (2 - (3 / 2 : ℝ)) := Real.one_lt_rpow (by norm_num) (by norm_num)
      rw [show (3 / 2 : ℝ) - 2 = -(2 - 3 / 2) by norm_num,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      exact inv_lt_one_of_one_lt₀ h3
    have h4 : 0 < 1 - Real.exp (max (9 / 2 : ℝ) 0 - 49 / 10) := by linarith
    have h5 : 0 < 1 - (2 : ℝ) ^ ((3 / 2 : ℝ) - 2) := by linarith
    positivity
  -- the constant of the `λ₁`-saving branch
  set K₂ : ℝ := K₂low Cn C₀ + K₃high Cc with hK₂def
  have hK₂pos : 0 < K₂ := by
    rw [hK₂def]
    have h1 : 1 ≤ K₂low Cn C₀ := le_max_left _ _
    have h2 : 0 ≤ K₃high Cc := le_trans (by norm_num) (le_max_left _ _)
    linarith
  set R : ℝ := 20 + 1 / Csi + 1 / Real.sqrt Cₛ with hRdef
  refine ⟨max (Kf / σ) K₂, lt_max_of_lt_left (div_pos hKfpos hσpos),
    max 2 (max q₀rep (max q₀zfr (max (Nat.ceil (Real.exp R)) q₀exp))), ?_⟩
  intro q hqN _inst χ₁ β₁ hχ hsq hβ hz hlam10
  have h2q : 2 ≤ q := le_trans (le_max_left _ _) hqN
  have hq2 : 1 < q := by omega
  have hr1 : max q₀rep (max q₀zfr (max (Nat.ceil (Real.exp R)) q₀exp)) ≤ q :=
    le_trans (le_max_right _ _) hqN
  have hr2 : max q₀zfr (max (Nat.ceil (Real.exp R)) q₀exp) ≤ q :=
    le_trans (le_max_right _ _) hr1
  have hr3 : max (Nat.ceil (Real.exp R)) q₀exp ≤ q := le_trans (le_max_right _ _) hr2
  have hq₀rep : q₀rep ≤ q := le_trans (le_max_left _ _) hr1
  have hq₀zfr : q₀zfr ≤ q := le_trans (le_max_left _ _) hr2
  have hqR : Nat.ceil (Real.exp R) ≤ q := le_trans (le_max_left _ _) hr3
  have hq₀exp : q₀exp ≤ q := le_trans (le_max_right _ _) hr3
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq2)
  have h𝓛R : R ≤ Real.log (q : ℝ) := by
    have h1 : Real.exp R ≤ (q : ℝ) := by
      have h2 : Real.exp R ≤ (Nat.ceil (Real.exp R) : ℝ) := Nat.le_ceil _
      exact le_trans h2 (by exact_mod_cast hqR)
    have h3 : Real.log (Real.exp R) ≤ Real.log (q : ℝ) := Real.log_le_log (by positivity) h1
    rwa [Real.log_exp] at h3
  have h𝓛20 : 20 ≤ Real.log (q : ℝ) := by
    have h1 : 20 ≤ R := by
      rw [hRdef]
      have h2 : 0 < 1 / Real.sqrt Cₛ := by positivity
      have h3 : 0 ≤ 1 / Csi := by positivity
      linarith
    linarith
  have hlog1 : 1 ≤ Real.log (q : ℝ) := by linarith
  have hq16 : 16 ≤ q := by
    have h1 : (16 : ℝ) < (q : ℝ) := by
      have h2 : (16 : ℝ) < Real.exp (20 : ℝ) := by
        rw [← Real.exp_log (by norm_num : (0 : ℝ) < 16)]
        refine Real.exp_lt_exp.mpr ?_
        have h6 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 16)
        linarith
      have h3 : Real.exp (20 : ℝ) ≤ (q : ℝ) := by
        have h4 : Real.exp (20 : ℝ) ≤ Real.exp (Real.log (q : ℝ)) := Real.exp_le_exp.mpr h𝓛20
        rwa [Real.exp_log (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q))] at h4
      linarith
    exact_mod_cast h1.le
  have hCsilog : (1 : ℝ) ≤ Csi * Real.log (q : ℝ) := by
    have h1 : 1 / Csi ≤ Real.log (q : ℝ) := by
      have h2 : 1 / Csi ≤ R := by
        rw [hRdef]
        have h3 : 0 < 1 / Real.sqrt Cₛ := by positivity
        linarith
      linarith
    rw [div_le_iff₀ hCsipos] at h1
    linarith [h1]
  have hCsL2 : (1 : ℝ) ≤ Cₛ * Real.log (q : ℝ) ^ 2 := by
    have h1 : 1 / Real.sqrt Cₛ ≤ Real.log (q : ℝ) := by
      have h2 : 1 / Real.sqrt Cₛ ≤ R := by
        rw [hRdef]
        have h3 : 0 ≤ 1 / Csi := by positivity
        linarith
      linarith
    have h3 : Real.sqrt Cₛ * (1 / Real.sqrt Cₛ) = 1 := by
      field_simp [ne_of_gt (Real.sqrt_pos.mpr hCₛpos)]
    have h4 : (1 : ℝ) ≤ Real.sqrt Cₛ * Real.log (q : ℝ) := by
      nlinarith [h1, hCₛpos, h3, Real.sqrt_pos.mpr hCₛpos]
    nlinarith [h4, Real.sq_sqrt hCₛpos.le, sq_nonneg (Real.log (q : ℝ))]
  have hlampos : 0 < lamOf q (β₁ : ℂ) := Work.LinnikAreas.Siegel.lamOf_pos hχ hβ hz
  have hCsi_app : Csi * Real.log (q : ℝ) / Real.sqrt (q : ℝ) ≤ lamOf q (β₁ : ℂ) :=
    hCsi q (by omega) χ₁ β₁ hχ hsq hβ hz
  have hCₛ_app : Cₛ * Real.log (q : ℝ) / (q : ℝ) ^ (1 / 200 : ℝ) ≤ lamOf q (β₁ : ℂ) :=
    hCₛ q (by omega) χ₁ β₁ hχ hsq hβ hz
  have hαhalf : Real.log (1 / lamOf q (β₁ : ℂ)) ≤ Real.log (q : ℝ) / 2 := by
    have h3 : 1 / lamOf q (β₁ : ℂ) ≤ Real.sqrt (q : ℝ) / (Csi * Real.log (q : ℝ)) := by
      rw [div_le_div_iff₀ hlampos (mul_pos hCsipos hlog)]
      have h4 : Csi * Real.log (q : ℝ) ≤ lamOf q (β₁ : ℂ) * Real.sqrt (q : ℝ) := by
        rw [div_le_iff₀ (Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)))]
          at hCsi_app
        linarith [hCsi_app]
      linarith [h4]
    calc Real.log (1 / lamOf q (β₁ : ℂ))
        ≤ Real.log (Real.sqrt (q : ℝ) / (Csi * Real.log (q : ℝ))) :=
          Real.log_le_log (by positivity) h3
      _ = Real.log (q : ℝ) / 2 - Real.log (Csi * Real.log (q : ℝ)) := by
          have h1 : Real.log (Real.sqrt (q : ℝ) / (Csi * Real.log (q : ℝ)))
              = Real.log (Real.sqrt (q : ℝ)) - Real.log (Csi * Real.log (q : ℝ)) :=
            Real.log_div
              (ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q))))
              (ne_of_gt (mul_pos hCsipos hlog))
          have h2 : Real.log (Real.sqrt (q : ℝ)) = Real.log (q : ℝ) / 2 :=
            Real.log_sqrt (by positivity)
          rw [h1, h2]
      _ ≤ Real.log (q : ℝ) / 2 := by
          have h5 : 0 ≤ Real.log (Csi * Real.log (q : ℝ)) := Real.log_nonneg hCsilog
          linarith
  have hhy : 1 / ((q : ℝ) ^ (1 / 100 : ℝ) * Real.log (q : ℝ)) < lamOf q (β₁ : ℂ) := by
    have h1 : 1 / ((q : ℝ) ^ (1 / 100 : ℝ) * Real.log (q : ℝ))
        < Cₛ * Real.log (q : ℝ) / (q : ℝ) ^ (1 / 200 : ℝ) := by
      rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) ^ (1 / 100 : ℝ) * Real.log (q : ℝ))
        (by positivity : (0 : ℝ) < (q : ℝ) ^ (1 / 200 : ℝ))]
      have h2 : (q : ℝ) ^ (1 / 200 : ℝ) < (q : ℝ) ^ (1 / 100 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast hq2) (by norm_num)
      have h3 : (q : ℝ) ^ (1 / 100 : ℝ)
          ≤ (q : ℝ) ^ (1 / 100 : ℝ) * (Cₛ * Real.log (q : ℝ) ^ 2) :=
        le_mul_of_one_le_right (Real.rpow_nonneg (by positivity) _) hCsL2
      calc (1 : ℝ) * (q : ℝ) ^ (1 / 200 : ℝ) < (q : ℝ) ^ (1 / 100 : ℝ) := by simpa using h2
        _ ≤ (q : ℝ) ^ (1 / 100 : ℝ) * (Cₛ * Real.log (q : ℝ) ^ 2) := h3
        _ = (Cₛ * Real.log (q : ℝ)) * ((q : ℝ) ^ (1 / 100 : ℝ) * Real.log (q : ℝ)) := by ring
    linarith [hCₛ_app]
  have hrepq : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), zeroMult χ ρ ≠ 0 →
      ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) → lamOf q (β₁ : ℂ) ≤ lamOf q ρ →
      (Real.log (1 / lamOf q (β₁ : ℂ))
          - Real.log (C₀ * ((11 / 5 : ℝ) + (11 / 10 : ℝ) * (Real.log (5 + |ρ.im|) / Real.log q))))
        / ((11 / 5 : ℝ) + (11 / 10 : ℝ) * (Real.log (5 + |ρ.im|) / Real.log q))
        ≤ lamOf q ρ :=
    fun χ ρ hzm' hne hle =>
      hrepall q hq₀rep χ₁ β₁ hχ hsq hβ hz hhy hlam10 χ ρ hzm' hne hle
  -- the two local family counts of `WindowBoundHyp`, and Siegel's `λ₁ ≫ e^{-(7/250)𝓛}`
  have hfam₁ : ∀ (σ' T : ℝ), 93 / 100 ≤ σ' → σ' ≤ 1 → 1 ≤ T →
      Work.ZeroDensity.famCount q σ' T
        ≤ Cn * Real.exp ((5 / 2) * ((1 - σ') * Real.log (q : ℝ))) * T ^ (3 / 2 : ℝ) :=
    fun σ' T h1 h2 h3 => hnear q (by omega) σ' T h1 h2 h3
  have hfam₂ : ∀ (σ' T : ℝ), 0 ≤ σ' → σ' ≤ 1 → 1 ≤ T →
      Work.ZeroDensity.famCount q σ' T
        ≤ Cc * Real.exp ((9 / 2) * ((1 - σ') * Real.log (q : ℝ))) * T ^ (3 / 2 : ℝ) :=
    fun σ' T h1 h2 h3 => hcrude q (by omega) σ' T h1 h2 h3
  have hexp_lam : Real.exp (-(7 / 250) * Real.log (q : ℝ)) ≤ lamOf q (β₁ : ℂ) := by
    have h := hexpall q hq₀exp χ₁ β₁ hχ hsq hβ hz
    simpa only [neg_mul] using h
  have h2p : (Real.log (q : ℝ)) ^ (-2 : ℝ) ≤ (Real.log (q : ℝ)) ^ (-(3 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlog1 (by norm_num)
  -- the per-finite-set bound, one branch per regime
  let p : DirichletCharacter ℂ q × ℂ → Prop := fun z =>
    zeroMult z.1 z.2 ≠ 0 ∧ 1 < |z.2.im| ∧ ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ))
  let F : DirichletCharacter ℂ q × ℂ → ℝ := fun z =>
    if p z then (zeroMult z.1 z.2 : ℝ)
      * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖ else 0
  have hFnn : 0 ≤ F := fun z => by
    simp only [F]
    split_ifs with hp
    · exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
    · exact le_refl 0
  have hbound : ∀ u : Finset (DirichletCharacter ℂ q × ℂ),
      ∑ z ∈ u, F z
        ≤ max (Kf / σ) K₂ * lamOf q (β₁ : ℂ) * (Real.log q) ^ (-(3 / 2) : ℝ) := by
    intro u
    have hsum_eq : ∑ z ∈ u, F z = ∑ z ∈ u.filter p, F z := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro z hz hnotin
      have hp : ¬ p z := fun hpp => hnotin (Finset.mem_filter.mpr ⟨hz, hpp⟩)
      simp only [F]; rw [if_neg hp]
    have hSF : ∑ z ∈ u.filter p, F z = ∑ z ∈ u.filter p, (zeroMult z.1 z.2 : ℝ)
        * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖ := by
      refine Finset.sum_congr rfl (fun z hz => ?_)
      have hp : p z := (Finset.mem_filter.mp hz).2
      simp only [F]; rw [if_pos hp]
    rw [hsum_eq, hSF]
    by_cases hbig : σ ≤ lamOf q (β₁ : ℂ)
    · -- `λ₁ ≥ σ`: the `λ₁`-free crude count suffices
      have hfree : (∑ z ∈ u.filter p, (zeroMult z.1 z.2 : ℝ)
            * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
          ≤ Kf * (Real.log q) ^ (-2 : ℝ) := by
        rw [hKfdef]
        exact crudeFreeFinsetBound hq2 χ₁ (β₁ : ℂ) hCcpos hfam₂ (u.filter p)
          (fun z hz => (Finset.mem_filter.mp hz).2.1)
          (fun z hz => (Finset.mem_filter.mp hz).2.2.1)
          (fun z hz => (Finset.mem_filter.mp hz).2.2.2)
      have hσinv : (1 : ℝ) ≤ (1 / σ) * lamOf q (β₁ : ℂ) := by
        rw [div_mul_eq_mul_div, one_mul]
        exact (le_div_iff₀ hσpos).mpr (by linarith [hbig])
      have hK2nn : 0 ≤ Kf * (Real.log (q : ℝ)) ^ (-2 : ℝ) :=
        mul_nonneg hKfpos.le (Real.rpow_nonneg hlog.le _)
      have hC1 : 0 ≤ (Kf / σ) * lamOf q (β₁ : ℂ) :=
        mul_nonneg (div_pos hKfpos hσpos).le hlampos.le
      calc (∑ z ∈ u.filter p, (zeroMult z.1 z.2 : ℝ)
            * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
          ≤ Kf * (Real.log q) ^ (-2 : ℝ) := hfree
        _ ≤ Kf * (Real.log q) ^ (-2 : ℝ) * ((1 / σ) * lamOf q (β₁ : ℂ)) :=
            le_mul_of_one_le_right hK2nn hσinv
        _ = (Kf / σ) * lamOf q (β₁ : ℂ) * (Real.log q) ^ (-2 : ℝ) := by ring
        _ ≤ (Kf / σ) * lamOf q (β₁ : ℂ) * (Real.log q) ^ (-(3 / 2) : ℝ) :=
            mul_le_mul_of_nonneg_left h2p hC1
        _ ≤ max (Kf / σ) K₂ * lamOf q (β₁ : ℂ) * (Real.log q) ^ (-(3 / 2) : ℝ) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_left _ _) hlampos.le)
              (Real.rpow_nonneg hlog.le _)
    · -- `λ₁ < σ`: the two-regime window bound `WindowBoundHyp`
      have hsmallσ : lamOf q (β₁ : ℂ) < σ := not_le.mp hbig
      have hsep : ∀ z ∈ u.filter p, lamOf q z.2 < lamOf q (β₁ : ℂ) →
          4 * (q : ℝ) ^ 2 ≤ |z.2.im| := by
        intro z hzmem hlt
        exact Work.LinnikAreas.BGTZ.height_sep_of_ZFR (q := q) (cZ := cZ) hq16
          (hzfrall q hq₀zfr) hχ hsq hβ hz
          (lt_of_lt_of_le hsmallσ hσ10) (lt_of_lt_of_le hsmallσ hσcZ)
          (Finset.mem_filter.mp hzmem).2.1 hlt
      have hWB := hw Cn Cc C₀ hCnpos hCcpos hC₀ (q := q) hq2 χ₁ (β₁ : ℝ) hfam₁ hfam₂ hrepq
        hlampos (lt_of_lt_of_le hsmallσ hσC₀) (lt_of_le_of_lt hlam10 (by norm_num)) hαhalf h𝓛20
        (u.filter p)
        (fun z hz => (Finset.mem_filter.mp hz).2.1)
        (fun z hz => (Finset.mem_filter.mp hz).2.2.1)
        (fun z hz => (Finset.mem_filter.mp hz).2.2.2)
        hsep
      have hK₂low_nn : 0 ≤ K₂low Cn C₀ := le_trans (by norm_num) (le_max_left _ _)
      have hK₃high_nn : 0 ≤ K₃high Cc := le_trans (by norm_num) (le_max_left _ _)
      have hinner : K₂low Cn C₀ * lamOf q (β₁ : ℂ)
            + K₃high Cc * Real.exp (-(7 / 250) * Real.log (q : ℝ))
          ≤ (K₂low Cn C₀ + K₃high Cc) * lamOf q (β₁ : ℂ) := by
        have h1 : K₃high Cc * Real.exp (-(7 / 250) * Real.log (q : ℝ))
            ≤ K₃high Cc * lamOf q (β₁ : ℂ) :=
          mul_le_mul_of_nonneg_left hexp_lam hK₃high_nn
        nlinarith [h1]
      have hK₂nn : 0 ≤ (K₂low Cn C₀ + K₃high Cc) * lamOf q (β₁ : ℂ) :=
        mul_nonneg (by linarith) hlampos.le
      have hmono : (K₂low Cn C₀ + K₃high Cc) * lamOf q (β₁ : ℂ)
          ≤ max (Kf / σ) K₂ * lamOf q (β₁ : ℂ) := by
        rw [hK₂def]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) hlampos.le
      calc (∑ z ∈ u.filter p, (zeroMult z.1 z.2 : ℝ)
            * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
          ≤ (K₂low Cn C₀ * lamOf q (β₁ : ℂ)
              + K₃high Cc * Real.exp (-(7 / 250) * Real.log (q : ℝ)))
              * (Real.log q) ^ (-2 : ℝ) := hWB
        _ ≤ (K₂low Cn C₀ + K₃high Cc) * lamOf q (β₁ : ℂ) * (Real.log q) ^ (-2 : ℝ) :=
            mul_le_mul_of_nonneg_right hinner (Real.rpow_nonneg hlog.le _)
        _ ≤ (K₂low Cn C₀ + K₃high Cc) * lamOf q (β₁ : ℂ) * (Real.log q) ^ (-(3 / 2) : ℝ) :=
            mul_le_mul_of_nonneg_left h2p hK₂nn
        _ ≤ max (Kf / σ) K₂ * lamOf q (β₁ : ℂ) * (Real.log q) ^ (-(3 / 2) : ℝ) :=
            mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg hlog.le _)
  have hgoal := restHighZeroSumFinset χ₁ (β₁ : ℂ)
    (C := max (Kf / σ) K₂ * lamOf q (β₁ : ℂ) * (Real.log q) ^ (-(3 / 2) : ℝ))
    (fun u => by simpa only [p, F] using hbound u)
  rw [show (-3 / 2 : ℝ) = -(3 / 2) by norm_num]
  exact hgoal

end

end Work.SiegelAbsorb
