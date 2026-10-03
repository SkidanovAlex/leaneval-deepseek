/-
# The assembly interface for `Work.KMTPlan.A6.ssuBtwistExBdd`

This module isolates the *single* remaining obligation of the proof of
`Work.KMTPlan.A6.ssuBtwistExBdd`: the "large `L`" case of the single-scale estimate, stated with
a constant `Cm` that is **uniform** in `(l₁, l₂, u)` as long as `max l₁ l₂` is above a threshold
`L₀`.

The route (see `NOTES_A6_ssuBtwistExBdd_SESSION.md`) is:

* `BtwistEx ρ P l₁ l₂ m_* m̃_* A B = Σ_{αβ} mZ(arithQ ρ L) α β · A_α · B_β` (child
  `ssuCollapse`), with `A := Tm ρ l₁ φ f`, `A_α := iwConv {α} (periodize φ) f`;
* `Ã_N(A,B) = Σ_{αβ} ssuCoeff P N α β · A_α · B_β + (error ≤ ssuErr P u N)` at `N := 2^E`
  (child `ssuAverageModel`, whose shift-modulation input is the proved `ssuShiftMod`);
* the deviation `Σ (ssuCoeff - ½ mZ) A_α B_β` bounded by `3·Qb·Nb/N` with the *sharp* denominators
  `q₁ ∈ iwP ρ l₁`, `q₂ ∈ iwP ρ l₂` (children `ssuDeviation`, `ssuDeviationSum`,
  `iwP_element_le_sharp`, `iw_height_card_le`);
* `‖Ã_N(A,B)‖₁ ≤ C_I (2^{-c_I l} + (Log N)^{-c_I/ρ}) ‖A‖₂‖B‖₂` from `hI : ImprovKMT P` with
  `l := L - 1`, its minor-arc hypothesis being supplied by `ssuProjZero` (which uses
  `ssuBandLimited`, `kmtProj_eq_zero_of_band_separation`) with the separation supplied by `ssuSep`;
* the numerical bookkeeping is the child `ssuBookkeeping`;
* the geometry (`NonAliasing`, support of `periodize φ`) is `ssuNonAliasing` and
  `supportedInArc_periodize_of_support`.

`ssuFromMain` below is the wrapper: it combines the crude bound `ssuCrudeUniform` (valid below
the threshold `L₀`) with `ssuMainBound` above it, and produces the conclusion of
`ssuBtwistExBdd` for each `ρ` (with `ρ₀ := 1`, `c := c_I/2`).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.ssuDevSumSelf
import Submission.Work.KMTPlan.A6.ssuCollapse

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier Work.KMTAreas.A7
open Submission.PointwiseErgodicTheorems

/-- **The large-`L` case of the single-scale estimate** (the only remaining obligation of
`ssuBtwistExBdd`).  See the module docstring for the route and the children it consumes. -/
theorem ssuMainBound (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ)
    (hd : 2 ≤ P.natDegree) (cI : ℝ) (hcI : 0 < cI) (CI : ℝ) (hCI : 0 ≤ CI)
    (hIρ : ∀ (N l : ℕ) (f g : ℤ → ℂ), 1 ≤ N → MemLp f 2 Measure.count →
      MemLp g 2 Measure.count →
      (Work.KMTContract.kmtProj ρ l (-(Work.Analysis.EndVar.logN N) + (l : ℤ)) f = 0 ∨
        Work.KMTContract.kmtProj ρ l
          ((P.natDegree : ℤ) * (-(Work.Analysis.EndVar.logN N) + (l : ℤ))) g = 0) →
      eLpNorm (fun x : ℤ => AhalfR TZ (N : ℝ≥0) Polynomial.X P f g x) 1 Measure.count
        ≤ ENNReal.ofReal (CI * ((2 : ℝ) ^ (-(cI * (l : ℝ)))
            + (((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) ^ (-(cI / ρ))))
          * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count) :
    ∃ Cm : ℝ, 0 < Cm ∧ ∃ L₀ : ℕ, 1 ≤ L₀ ∧
      ∀ (l₁ l₂ u : ℕ) (φ ψ : ℝ → ℂ) (f g : ℤ → ℂ),
        L₀ ≤ max l₁ l₂ → (max l₁ l₂ : ℝ) ≤ (u : ℝ) →
        (2 : ℝ) ^ (ρ * (max l₁ l₂ : ℝ)) ≤ (u : ℝ) →
        MemLp f 2 Measure.count → MemLp g 2 Measure.count →
        MemLp (periodize φ) ⊤ circleMeasure → MemLp (periodize ψ) ⊤ circleMeasure →
        (∀ ξ : ℝ, φ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(3 * (u : ℤ)))) →
        (∀ ξ : ℝ, ψ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ)))) →
        eLpNorm (fun x : ℤ => BtwistEx ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
            (Tm ρ l₁ φ f) (Tm ρ l₂ ψ g) x) 1 Measure.count
          ≤ ENNReal.ofReal Cm
            * ENNReal.ofReal ((2 : ℝ) ^ (-((cI / 2) * (max l₁ l₂ : ℝ))))
            * eLpNorm (Tm ρ l₁ φ f) 2 Measure.count
            * eLpNorm (Tm ρ l₂ ψ g) 2 Measure.count := by
  classical
  obtain ⟨Cπ, hCπpos, hCπle⟩ := iwP_element_le_sharp ρ hρ hρ1
  obtain ⟨Csh₀, hCsh₀pos, hCsh₀le⟩ := iw_height_card_le (ρ := ρ) hρ
  obtain ⟨Cna, hCnapos, hCna⟩ := ssuNonAliasing ρ hρ hρ1
  obtain ⟨Csep, hCseppos, hCsep⟩ := ssuSep ρ hρ hρ1
  have hCsh : ∃ Csh : ℝ, 1 ≤ Csh ∧ ∀ l : ℕ,
      ((iwArithFreqs ρ l).card : ℝ)
        ≤ Csh * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l : ℝ))) := by
    refine ⟨max 1 Csh₀, le_max_left _ _, fun l => ?_⟩
    refine (hCsh₀le l).trans ?_
    have h1 : (0 : ℝ) < (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l : ℝ))) :=
      Real.rpow_pos_of_pos (by norm_num) _
    exact mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) Csh₀) h1.le
  obtain ⟨Csh, hCsh1, hCshle⟩ := hCsh
  let Kdev : ℝ := 2 * Cπ + Real.logb 2 (6 * Csh ^ 2) + cI / 2
  let Kerr : ℝ := Real.logb 2 (8 * Real.pi * (ssuPc P + 2))
  have hKdev0 : 0 ≤ Kdev := by
    have h1 : (1 : ℝ) ≤ 6 * Csh ^ 2 := by nlinarith [hCsh1]
    have h2 : 0 ≤ Real.logb 2 (6 * Csh ^ 2) := by
      rw [Real.logb]
      exact div_nonneg (Real.log_nonneg h1) (Real.log_pos one_lt_two).le
    change 0 ≤ 2 * Cπ + Real.logb 2 (6 * Csh ^ 2) + cI / 2
    linarith [hCπpos.le, h2, div_nonneg hcI.le (by norm_num : (0 : ℝ) ≤ 2)]
  have hKerr0 : 0 ≤ Kerr := by
    have hsc : (0 : ℝ) ≤ ssuPc P := ssuPc_nonneg P
    have h1 : (1 : ℝ) < 8 * Real.pi * (ssuPc P + 2) := by
      have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
      nlinarith
    change 0 ≤ Real.logb 2 (8 * Real.pi * (ssuPc P + 2))
    rw [Real.logb]
    exact div_nonneg (Real.log_nonneg h1.le) (Real.log_pos one_lt_two).le
  obtain ⟨L₀, hL₀1, hL₀⟩ := ssuBookkeeping ρ hρ hρ1 cI hcI Cna Csep Kdev Kerr
    hCnapos.le hCseppos.le hKdev0 hKerr0
  refine ⟨2 * CI * (2 ^ cI + 1) + 2, ?_, L₀, hL₀1, ?_⟩
  · have h1 : (0 : ℝ) < 2 ^ cI := Real.rpow_pos_of_pos (by norm_num) cI
    nlinarith
  intro l₁ l₂ u φ ψ f g hLu hLuR h2ρL hf hg hΦ hΨ hφ hψ
  set L : ℕ := max l₁ l₂ with hLdef
  have hLcast : max (l₁ : ℝ) (l₂ : ℝ) = (L : ℝ) := by rw [hLdef, Nat.cast_max]
  rw [hLcast] at hLuR h2ρL ⊢
  obtain ⟨E, hE2, hEρ, hCnaL, hCsep3u, hCsepE, hEdev, hEu⟩ := hL₀ L u hLu hLuR h2ρL
  set N : ℕ := 2 ^ E with hNdef
  have hL1 : 1 ≤ L := le_trans hL₀1 hLu
  have hLuNat : L ≤ u := by exact_mod_cast hLuR
  have hu1 : 1 ≤ u := le_trans hL1 hLuNat
  have hdc : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
  have hud : (1 : ℝ) ≤ (P.natDegree : ℝ) := by linarith
  have hu0 : (0 : ℝ) ≤ (u : ℝ) := Nat.cast_nonneg u
  have hN1 : 1 ≤ N := by rw [hNdef]; exact Nat.one_le_two_pow
  have hNcast : ((N : ℝ)) = (2 : ℝ) ^ E := by
    rw [hNdef, Nat.cast_pow]; norm_num
  have hlogN : Work.Analysis.EndVar.logN N = (E : ℤ) := by
    have h1 : Nat.log 2 (max N 2) = E := by
      have hmax : max N 2 = 2 ^ E := by
        rw [hNdef]
        exact max_eq_left (by
          have h : (2 : ℕ) = 2 ^ 1 := by norm_num
          rw [h]
          exact Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [hmax, Nat.log_pow (show (1 : ℕ) < 2 by norm_num)]
    simp only [Work.Analysis.EndVar.logN, h1]
  have hNA : ∀ (l : ℕ), l ≤ L → ∀ k : ℤ, 2 * (u : ℝ) ≤ -(k : ℝ) →
      NonAliasing k (diffFreqs ρ l) := by
    intro l hl k hk
    have hCnaL' : Cna * (1 + (L : ℝ) * (2 : ℝ) ^ (ρ * (L : ℝ) / 2) + (L : ℝ)) + 2
        ≤ 2 * (u : ℝ) := hCnaL
    have hmono : (1 + (l : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2) + (l : ℝ))
        ≤ (1 + (L : ℝ) * (2 : ℝ) ^ (ρ * (L : ℝ) / 2) + (L : ℝ)) :=
      ssuPhi_mono hρ.le hl
    have h3 : Cna * (1 + (l : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2) + (l : ℝ))
        ≤ Cna * (1 + (L : ℝ) * (2 : ℝ) ^ (ρ * (L : ℝ) / 2) + (L : ℝ)) :=
      mul_le_mul_of_nonneg_left hmono hCnapos.le
    refine hCna l k ?_
    linarith
  have hNA3u₁ : NonAliasing (-(3 * (u : ℤ))) (diffFreqs ρ l₁) :=
    hNA l₁ (le_max_left _ _) _ (by push_cast; nlinarith [hu0])
  have hNA2u₁ : NonAliasing (-(2 * (u : ℤ))) (diffFreqs ρ l₁) :=
    hNA l₁ (le_max_left _ _) _ (by push_cast; nlinarith [hu0])
  have hNA3du₂ : NonAliasing (-(3 * ((P.natDegree : ℤ) * (u : ℤ)))) (diffFreqs ρ l₂) :=
    hNA l₂ (le_max_right _ _) _ (by push_cast; nlinarith [hu0, hud])
  have hNA2du₂ : NonAliasing (-(2 * ((P.natDegree : ℤ) * (u : ℤ)))) (diffFreqs ρ l₂) :=
    hNA l₂ (le_max_right _ _) _ (by push_cast; nlinarith [hu0, hud])
  have hSupp₁ : SupportedInArc (-(3 * (u : ℤ))) (periodize φ) :=
    supportedInArc_periodize_of_support u hu1 φ hφ
  have hSupp₂ : SupportedInArc (-(3 * ((P.natDegree : ℤ) * (u : ℤ)))) (periodize ψ) := by
    have h1 : 1 ≤ P.natDegree := le_trans (by norm_num : (1 : ℕ) ≤ 2) hd
    have hpos : 1 ≤ P.natDegree * u := by
      calc (1 : ℕ) = 1 * 1 := by norm_num
        _ ≤ P.natDegree * u := Nat.mul_le_mul h1 hu1
    have h := supportedInArc_periodize_of_support (P.natDegree * u) hpos ψ
      (fun ξ hξ => by simpa only [Nat.cast_mul, mul_assoc] using hψ ξ hξ)
    simpa only [Nat.cast_mul, mul_assoc] using h
  have hSupp₂' : SupportedInArc (-(3 * (u : ℤ))) (periodize ψ) := by
    intro ξ hξ
    obtain ⟨θ, hθ, hθξ⟩ := hSupp₂ ξ hξ
    refine ⟨θ, ?_, hθξ⟩
    rw [realArc, Set.mem_Icc] at hθ ⊢
    have hle : (2 : ℝ) ^ (-(3 * ((P.natDegree : ℤ) * (u : ℤ))))
        ≤ (2 : ℝ) ^ (-(3 * (u : ℤ))) := by
      refine zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ?_
      have h1 : (1 : ℤ) ≤ (P.natDegree : ℤ) := by
        exact_mod_cast (le_trans (by norm_num : (1 : ℕ) ≤ 2) hd)
      have h2 : (0 : ℤ) ≤ (u : ℤ) := Int.natCast_nonneg u
      have h3 : (u : ℤ) ≤ (P.natDegree : ℤ) * (u : ℤ) := by
        calc (u : ℤ) = 1 * (u : ℤ) := by ring
          _ ≤ (P.natDegree : ℤ) * (u : ℤ) := mul_le_mul_of_nonneg_right h1 h2
      nlinarith [h3]
    constructor <;> linarith [hθ.1, hθ.2]
  have hsep₁ : ∀ α ∈ iwArithFreqs ρ (L - 1), ∀ β ∈ diffFreqs ρ L,
      (2 : ℝ) ^ ((L : ℤ) - 1 - (E : ℤ)) + (2 : ℝ) ^ (-(3 * (u : ℤ))) < ‖β - α‖ :=
    hCsep L u ((L : ℤ) - 1 - (E : ℤ)) hL1 (hCsep3u L le_rfl) (by
      have h := hCsepE L le_rfl
      have hk : -(((L : ℤ) - 1 - (E : ℤ) : ℤ) : ℝ) = (E : ℝ) - (L : ℝ) + 1 := by
        push_cast; ring
      rw [hk]
      linarith)
  have hsep₂ : ∀ α ∈ iwArithFreqs ρ (L - 1), ∀ β ∈ diffFreqs ρ L,
      (2 : ℝ) ^ ((P.natDegree : ℤ) * ((L : ℤ) - 1 - (E : ℤ)))
        + (2 : ℝ) ^ (-(3 * (u : ℤ))) < ‖β - α‖ :=
    hCsep L u ((P.natDegree : ℤ) * ((L : ℤ) - 1 - (E : ℤ))) hL1 (hCsep3u L le_rfl) (by
      have h := hCsepE L le_rfl
      have hΦ0 : (0 : ℝ) ≤ 1 + (L : ℝ) * (2 : ℝ) ^ (ρ * (L : ℝ) / 2) + (L : ℝ) := by
        have h0 := ssuPhi_nonneg ρ L
        rwa [ssuPhi] at h0
      have hpos : (0 : ℝ) ≤ (E : ℝ) - (L : ℝ) + 1 := by
        have h2 : (0 : ℝ) ≤ Csep * (1 + (L : ℝ) * (2 : ℝ) ^ (ρ * (L : ℝ) / 2) + (L : ℝ)) :=
          mul_nonneg hCseppos.le hΦ0
        linarith
      have hk : -((((P.natDegree : ℤ) * ((L : ℤ) - 1 - (E : ℤ))) : ℤ) : ℝ)
          = (P.natDegree : ℝ) * ((E : ℝ) - (L : ℝ) + 1) := by push_cast; ring
      rw [hk]
      nlinarith [h, hpos, hud])
  have hproj₁ : Work.KMTContract.kmtProj ρ (L - 1) ((L : ℤ) - 1 - (E : ℤ))
      (Tm ρ L φ f) = 0 :=
    ssuProjZero ρ L hL1 u ((L : ℤ) - 1 - (E : ℤ)) φ f hΦ hSupp₁ hsep₁ hf
  have hproj₂ : Work.KMTContract.kmtProj ρ (L - 1)
      ((P.natDegree : ℤ) * ((L : ℤ) - 1 - (E : ℤ))) (Tm ρ L ψ g) = 0 :=
    ssuProjZero ρ L hL1 u ((P.natDegree : ℤ) * ((L : ℤ) - 1 - (E : ℤ))) ψ g
      hΨ hSupp₂' hsep₂ hg
  have hcastL1 : ((L - 1 : ℕ) : ℤ) = (L : ℤ) - 1 := by
    rw [Nat.cast_sub hL1]; norm_num
  have hkEq : -(Work.Analysis.EndVar.logN N) + ((L - 1 : ℕ) : ℤ)
      = (L : ℤ) - 1 - (E : ℤ) := by
    rw [hlogN, hcastL1]; ring
  have hdisj : Work.KMTContract.kmtProj ρ (L - 1)
        (-(Work.Analysis.EndVar.logN N) + ((L - 1 : ℕ) : ℤ)) (Tm ρ l₁ φ f) = 0
      ∨ Work.KMTContract.kmtProj ρ (L - 1)
        ((P.natDegree : ℤ) * (-(Work.Analysis.EndVar.logN N) + ((L - 1 : ℕ) : ℤ)))
        (Tm ρ l₂ ψ g) = 0 := by
    rcases max_cases l₁ l₂ with ⟨heq, _⟩ | ⟨heq, _⟩
    · left
      have heqL : L = l₁ := by rw [hLdef]; exact heq
      rw [hkEq, ← heqL]
      exact hproj₁
    · right
      have heqL : L = l₂ := by rw [hLdef]; exact heq
      rw [hkEq, ← heqL]
      exact hproj₂
  have hA_mem : MemLp (Tm ρ l₁ φ f) 2 Measure.count := ssuTmMemLp ρ l₁ φ f hΦ hf
  have hB_mem : MemLp (Tm ρ l₂ ψ g) 2 Measure.count := ssuTmMemLp ρ l₂ ψ g hΨ hg
  have himp0 := hIρ N (L - 1) (Tm ρ l₁ φ f) (Tm ρ l₂ ψ g) hN1 hA_mem hB_mem hdisj
  have hcastL : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
    rw [Nat.cast_sub hL1]; norm_num
  have hlogR : (((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) = (E : ℝ) := by
    rw [hlogN]; norm_num
  let E1 : ENNReal := eLpNorm (Tm ρ l₁ φ f) 2 Measure.count
  let E2 : ENNReal := eLpNorm (Tm ρ l₂ ψ g) 2 Measure.count
  let H : ℤ → ℂ := ssuAvg P N (Tm ρ l₁ φ f) (Tm ρ l₂ ψ g)
  let Qb : ℝ := (2 : ℝ) ^ (2 * Cπ * ssuPhi ρ L)
  let Nb : ℝ := Csh ^ 2 * (2 : ℝ) ^ (2 * (2 : ℝ) ^ (ρ * (L : ℝ)))
  let cH : ℝ := CI * ((2 : ℝ) ^ (-(cI * ((L : ℝ) - 1))) + (E : ℝ) ^ (-(cI / ρ)))
  let cE : ℝ := 2 * Real.pi * (((2 : ℝ) ^ E) * (2 : ℝ) ^ (-(3 * (u : ℤ)))
      + ssuPc P * (((2 : ℝ) ^ E) ^ P.natDegree)
        * (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ))))
  let cD : ℝ := 3 * Qb * Nb / (2 : ℝ) ^ E
  have hQb0 : (0 : ℝ) ≤ Qb := by
    dsimp only [Qb]; exact Real.rpow_nonneg (by norm_num) _
  have hNb0 : (0 : ℝ) ≤ Nb := by
    dsimp only [Nb]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (by norm_num) _)
  have hQbval : Qb = (2 : ℝ) ^ (2 * Cπ * ssuPhi ρ L) := rfl
  have hNbval : Nb = Csh ^ 2 * (2 : ℝ) ^ (2 * (2 : ℝ) ^ (ρ * (L : ℝ))) := rfl
  have hcEval : cE = ssuErr P u N := by
    dsimp only [cE]
    rw [hNdef]
    simp only [ssuErr, Nat.cast_pow, Nat.cast_ofNat]
  have hcDval : cD = 3 * Qb * Nb / (N : ℝ) := by
    dsimp only [cD]
    rw [hNcast]
  have hargE : CI * ((2 : ℝ) ^ (-(cI * ((L - 1 : ℕ) : ℝ)))
        + (((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) ^ (-(cI / ρ)))
      = CI * ((2 : ℝ) ^ (-(cI * ((L : ℝ) - 1))) + (E : ℝ) ^ (-(cI / ρ))) := by
    rw [hcastL, hlogR]
  have himp : eLpNorm H 1 Measure.count ≤ ENNReal.ofReal cH * E1 * E2 := by
    have hH : H = fun x : ℤ =>
        AhalfR TZ (N : ℝ≥0) Polynomial.X P (Tm ρ l₁ φ f) (Tm ρ l₂ ψ g) x := by
      funext x
      exact congrFun (ssuAvg_eq_AhalfR P N (Tm ρ l₁ φ f) (Tm ρ l₂ ψ g)) x
    rw [hH]
    refine himp0.trans (le_of_eq ?_)
    rw [hargE]
  let Mf : ℤ → ℂ := fun x => ∑ α ∈ diffFreqs ρ l₁, ∑ β ∈ diffFreqs ρ l₂,
      ssuCoeff P N α β * iwConv {α} (periodize φ) f x * iwConv {β} (periodize ψ) g x
  let Wf : ℤ → ℂ := fun x => ∑ α ∈ diffFreqs ρ l₁, ∑ β ∈ diffFreqs ρ l₂,
      mZ P (arithQ ρ (max l₁ l₂)) α β * iwConv {α} (periodize φ) f x
        * iwConv {β} (periodize ψ) g x
  let Df : ℤ → ℂ := fun x => ∑ α ∈ diffFreqs ρ l₁, ∑ β ∈ diffFreqs ρ l₂,
      (ssuCoeff P N α β - (2 : ℂ)⁻¹ * mZ P (arithQ ρ (max l₁ l₂)) α β)
        * iwConv {α} (periodize φ) f x * iwConv {β} (periodize ψ) g x
  have hmodel0 := ssuAverageModel ρ P hd l₁ l₂ u N φ ψ f g hN1 hu1 hΦ hΨ hφ hψ
    hNA3u₁ hNA3du₂ hf hg
  have hmodel : eLpNorm (fun x : ℤ => H x - Mf x) 1 Measure.count
      ≤ ENNReal.ofReal cE * E1 * E2 := by
    rw [show cE = ssuErr P u N from hcEval]
    exact hmodel0
  have hcollapse : (fun x : ℤ => BtwistEx ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
        (Tm ρ l₁ φ f) (Tm ρ l₂ ψ g) x) = Wf := by
    funext x
    exact ssuCollapse ρ P hd l₁ l₂ u φ ψ f g hΦ hΨ hφ hψ hu1 hNA2u₁ hNA2du₂ hf hg x
  have hper : ∀ (α β : SsuC) (q₁ q₂ : ℕ), α ∈ diffFreqs ρ l₁ → β ∈ diffFreqs ρ l₂ →
      q₁ ∈ iwP ρ l₁ → q₂ ∈ iwP ρ l₂ → q₁ • α = 0 → q₂ • β = 0 →
      ((q₁ * q₂ : ℕ) : ℝ) ≤ Qb := by
    intro α β q₁ q₂ hα hβ hq₁ hq₂ h1 h2
    rw [hQbval]
    exact ssuQbBound ρ hρ hρ1 Cπ hCπpos hCπle L l₁ l₂ α β q₁ q₂ hLdef.symm
      hα hβ hq₁ hq₂ h1 h2
  have hcard : ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ) ≤ Nb := by
    rw [hNbval]
    exact ssuNbBound ρ hρ hρ1 Csh hCsh1 hCshle L l₁ l₂ hLdef.symm
  have hdev0 := ssuDeviationSumSelf P ρ hρ hρ1 l₁ l₂ u N φ ψ f g Qb Nb hQb0 hNb0 hN1
    hΦ hΨ hSupp₁ hSupp₂ hNA3u₁ hNA3du₂ hper hcard hf hg
  have hdev : eLpNorm Df 1 Measure.count ≤ ENNReal.ofReal cD * E1 * E2 := by
    rw [show cD = 3 * Qb * Nb / (N : ℝ) from hcDval]
    exact hdev0
  have hDpt : ∀ x : ℤ, Mf x - (2 : ℂ)⁻¹ * Wf x = Df x := by
    intro x
    simp only [Mf, Wf, Df]
    rw [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    ring
  have hWfun : Wf = fun x : ℤ => (2 : ℂ) * (Mf x - Df x) := by
    funext x
    have h := hDpt x
    have h2 : (2 : ℂ) * (2 : ℂ)⁻¹ = 1 := by norm_num
    calc Wf x = (2 : ℂ) * ((2 : ℂ)⁻¹ * Wf x) := by rw [← mul_assoc, h2, one_mul]
      _ = (2 : ℂ) * (Mf x - Df x) := by
            have h4 : (2 : ℂ)⁻¹ * Wf x = Mf x - Df x := by rw [← h]; ring
            rw [h4]
  have hEnorm : eLpNorm Wf 1 Measure.count
      ≤ ENNReal.ofReal 2 * (eLpNorm H 1 Measure.count
          + eLpNorm (fun x : ℤ => H x - Mf x) 1 Measure.count
          + eLpNorm Df 1 Measure.count) := by
    rw [hWfun]
    rw [show (fun x : ℤ => (2 : ℂ) * (Mf x - Df x)) = (2 : ℂ) • (Mf - Df) from by
      funext x; rfl]
    rw [eLpNorm_const_smul]
    rw [show ‖(2 : ℂ)‖ₑ = ENNReal.ofReal 2 from by rw [enorm_eq_nnnorm]; norm_num]
    gcongr
    have h1 : eLpNorm (fun x : ℤ => Mf x - Df x) 1 Measure.count
        ≤ eLpNorm Mf 1 Measure.count + eLpNorm Df 1 Measure.count :=
      eLpNorm_sub_le (by norm_num : (1:ℝ≥0∞) ≤ 1)
    have h2 : eLpNorm Mf 1 Measure.count
        ≤ eLpNorm H 1 Measure.count + eLpNorm (fun x : ℤ => H x - Mf x) 1 Measure.count := by
      have hMf : Mf = H - fun y : ℤ => (H y - Mf y) := by
        funext x
        show Mf x = H x - (H x - Mf x)
        ring
      have hsub := eLpNorm_sub_le (p := 1) (μ := Measure.count) (f := H)
        (g := fun x : ℤ => (H x - Mf x)) (by norm_num : (1:ℝ≥0∞) ≤ 1)
      have hLHS : eLpNorm Mf 1 Measure.count
          = eLpNorm (H - fun y : ℤ => (H y - Mf y)) 1 Measure.count :=
        congrArg (fun g => eLpNorm g 1 Measure.count) hMf
      exact hLHS.le.trans hsub
    calc eLpNorm (fun x : ℤ => Mf x - Df x) 1 Measure.count
        ≤ eLpNorm Mf 1 Measure.count + eLpNorm Df 1 Measure.count := h1
      _ ≤ (eLpNorm H 1 Measure.count + eLpNorm (fun x : ℤ => H x - Mf x) 1 Measure.count)
            + eLpNorm Df 1 Measure.count := add_le_add h2 le_rfl
  have hcH0 : (0 : ℝ) ≤ cH := by
    dsimp only [cH]
    refine mul_nonneg hCI (add_nonneg ?_ ?_)
    · exact Real.rpow_nonneg (by norm_num) _
    · exact Real.rpow_nonneg (Nat.cast_nonneg E) _
  have hcE0 : (0 : ℝ) ≤ cE := by
    dsimp only [cE]
    refine mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (add_nonneg ?_ ?_)
    · exact mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) E)
        (zpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)
    · refine mul_nonneg (mul_nonneg (ssuPc_nonneg P) ?_) ?_
      · exact pow_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) E) P.natDegree
      · exact zpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _
  have hcD0 : (0 : ℝ) ≤ cD := by
    dsimp only [cD]
    have h2E : (0 : ℝ) < (2 : ℝ) ^ E := pow_pos (by norm_num : (0:ℝ) < 2) E
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hQb0) hNb0) h2E.le
  have hfinal : 2 * cH + 2 * cE + 2 * cD
      ≤ (2 * CI * (2 ^ cI + 1) + 2) * (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))) := by
    have harith := ssuArithFinal ρ cI CI Cπ Csh Kdev Kerr Qb Nb (ssuPc P) P.natDegree L E u
      hρ hcI hCI hCπpos.le hCsh1 (ssuPc_nonneg P) hQb0 hNb0 (by omega) le_rfl le_rfl
      hE2 hEρ rfl rfl hEdev hEu
    have hconv : 2 * cH + 2 * cE + 2 * cD
        = 2 * CI * ((2 : ℝ) ^ (-(cI * ((L : ℝ) - 1))) + (E : ℝ) ^ (-(cI / ρ)))
          + 2 * (2 * Real.pi * (((2 : ℝ) ^ E) * (2 : ℝ) ^ (-(3 * (u : ℤ)))
              + ssuPc P * (((2 : ℝ) ^ E) ^ P.natDegree)
                * (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ)))))
          + 6 * Qb * Nb / (2 : ℝ) ^ E := by
      dsimp only [cH, cE, cD]
      ring
    rw [hconv]
    exact harith
  calc eLpNorm (fun x : ℤ => BtwistEx ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
          (Tm ρ l₁ φ f) (Tm ρ l₂ ψ g) x) 1 Measure.count
      = eLpNorm Wf 1 Measure.count := by rw [hcollapse]
    _ ≤ ENNReal.ofReal 2 * (eLpNorm H 1 Measure.count
          + eLpNorm (fun x : ℤ => H x - Mf x) 1 Measure.count
          + eLpNorm Df 1 Measure.count) := hEnorm
    _ ≤ ENNReal.ofReal 2 * ((ENNReal.ofReal cH * E1 * E2)
          + (ENNReal.ofReal cE * E1 * E2)
          + (ENNReal.ofReal cD * E1 * E2)) := by
        gcongr
    _ = (ENNReal.ofReal (2 * cH) + ENNReal.ofReal (2 * cE) + ENNReal.ofReal (2 * cD)) * E1 * E2 := by
        rw [show ENNReal.ofReal 2 * (ENNReal.ofReal cH * E1 * E2 + ENNReal.ofReal cE * E1 * E2
              + ENNReal.ofReal cD * E1 * E2)
            = (ENNReal.ofReal 2 * ENNReal.ofReal cH + ENNReal.ofReal 2 * ENNReal.ofReal cE
              + ENNReal.ofReal 2 * ENNReal.ofReal cD) * E1 * E2 from by ring,
          show ENNReal.ofReal 2 * ENNReal.ofReal cH = ENNReal.ofReal (2 * cH)
            from (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)).symm,
          show ENNReal.ofReal 2 * ENNReal.ofReal cE = ENNReal.ofReal (2 * cE)
            from (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)).symm,
          show ENNReal.ofReal 2 * ENNReal.ofReal cD = ENNReal.ofReal (2 * cD)
            from (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)).symm]
    _ = ENNReal.ofReal (2 * cH + 2 * cE + 2 * cD) * E1 * E2 := by
        rw [show ENNReal.ofReal (2 * cH) + ENNReal.ofReal (2 * cE)
              = ENNReal.ofReal (2 * cH + 2 * cE) from (ENNReal.ofReal_add (by linarith) (by linarith)).symm,
          show ENNReal.ofReal (2 * cH + 2 * cE) + ENNReal.ofReal (2 * cD)
              = ENNReal.ofReal (2 * cH + 2 * cE + 2 * cD)
            from (ENNReal.ofReal_add (by linarith) (by linarith)).symm]
    _ ≤ ENNReal.ofReal ((2 * CI * (2 ^ cI + 1) + 2) * (2 : ℝ) ^ (-((cI / 2) * (L : ℝ))))
        * E1 * E2 := by
        gcongr
    _ = ENNReal.ofReal (2 * CI * (2 ^ cI + 1) + 2)
        * ENNReal.ofReal ((2 : ℝ) ^ (-((cI / 2) * (L : ℝ)))) * E1 * E2 := by
        rw [ENNReal.ofReal_mul (by positivity)]


end

end Work.KMTPlan.A6
