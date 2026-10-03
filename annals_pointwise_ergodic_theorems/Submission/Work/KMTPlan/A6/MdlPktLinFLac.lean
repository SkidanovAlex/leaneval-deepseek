/-
# From the low-pass estimate for the dyadic walk to the lacunary family

`Work.KMTPlan.A6.lowpassLac_of_lowpassVarAll`: the `LowpassVarAll` estimate (the existential-positive
crux-derived `ℓᵖ` variational bound for the *dyadic* low-pass walk
`m ↦ lpf ρ l₁ m₀ m f = kmtProj ρ l₁ (-(m₀+m)) f`) transfers to the *lacunary* family
`n ↦ Tle ρ l₁ (varphiN (⌊a n⌋) 0) f = kmtProj ρ l₁ (-(logN ⌊a n⌋)) f`, with constants free of the
lacunary sequence and of the base level.

This is the second step of the road recorded in `NOTES_MdlPktLinF_SESSION2.md`: it is the
`hLowpass` input of `Work.KMTAreas.A7.lacunaryBumpVarEstimate_assembly`.  The proof is the
reindexing argument of `Work.KMTAreas.A7.lacunaryIWProjLowpassVar` (that declaration is tainted by
the `sorry` of `chainPartSqFun` and is *not* used; only its proof pattern is copied, with
`LowpassVarAll` supplied as a hypothesis), namely: `GoodMajorArcs` forces `k ≤ 0`, the level map
`n ↦ logN ⌊a n⌋` is monotone, and the family is the monotone reindexing
`σ n = (logN ⌊a n⌋ + k).toNat` of the dyadic walk at the base level `m₀ = (-k).toNat`;
`variationalNorm_comp_mono_le` then transports the bound pointwise in `x`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlPktLinFDefs
import Submission.Work.KMTAreas.A7.lacunaryIWProjLowpassVar
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.KMTAreas.A7 Work.KMTAreas.A7Hi

noncomputable section

/-- A `Λ`-lacunary sequence with `Λ > 1` and `a n ≥ 1` is monotone. -/
theorem lowpass_monotone_of_lacunary' {Λ : NNReal} (hΛ : 1 < Λ) {a : ℕ → NNReal}
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) : Monotone a := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
  have h2 : Λ < a (n + 1) / a n := ha n
  have h1 : Λ * a n < a (n + 1) := by rwa [lt_div_iff₀ hpos] at h2
  have h3 : a n ≤ Λ * a n := by
    simpa using mul_le_mul_of_nonneg_right (le_of_lt hΛ) (le_of_lt hpos)
  exact le_trans h3 h1.le

/-- **The lacunary low-pass variational estimate from the dyadic one.** -/
theorem lowpassLac_of_lowpassVarAll (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (h : LowpassVarAll ρ) (r : NNReal) (hr : 2 < r) (p : ENNReal) (hp : 1 < p)
    (hptop : p < ⊤) (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (k : ℤ) (l₁ : ℕ) (a : ℕ → NNReal),
        PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) → ∀ f : ℤ → ℂ,
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ k →
        (∀ n : ℕ, -(Work.Analysis.EndVar.logN (Nat.floor (a n))) ≤ k) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₁
              (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0) f x))
          p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2) *
              MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  obtain ⟨Cρ, hCρpos, C, hCpos, hmain⟩ := h r hr p hp hptop
  refine ⟨Cρ, hCρpos, C, hCpos, ?_⟩
  intro k l₁ a ha ha1 f hgood hk
  -- `GoodMajorArcs` forces the window level to be non-positive
  have hk0 : k ≤ 0 := by
    have hpos : (0 : ℝ) < Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) := by
      have h2 := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (ρ * (l₁ : ℝ))
      positivity
    have h3 : (k : ℝ) ≤ 0 := by
      have h4 : (k : ℝ) ≤ -Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) := hgood
      linarith
    exact_mod_cast h3
  have hamono : Monotone a := lowpass_monotone_of_lacunary' hΛ ha ha1
  set m₀ : ℕ := (-k).toNat with hm₀def
  have hm₀ : ((m₀ : ℕ) : ℤ) = -k := by
    rw [hm₀def]
    exact Int.toNat_of_nonneg (by omega)
  have hgood' : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) := by
    rw [hm₀, neg_neg]
    exact hgood
  set σ : ℕ → ℕ := fun n => (Work.Analysis.EndVar.logN (Nat.floor (a n)) + k).toNat with hσdef
  have hσmono : Monotone σ := by
    intro n m hnm
    have h1 : Nat.floor (a n) ≤ Nat.floor (a m) := Nat.floor_mono (hamono hnm)
    have h2 : Work.Analysis.EndVar.logN (Nat.floor (a n))
        ≤ Work.Analysis.EndVar.logN (Nat.floor (a m)) := Work.Analysis.EndVar.logN_mono h1
    have h3 : (0 : ℤ) ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) + k := by
      have h := hk n; omega
    have h4 : (0 : ℤ) ≤ Work.Analysis.EndVar.logN (Nat.floor (a m)) + k := by
      have h := hk m; omega
    show (Work.Analysis.EndVar.logN (Nat.floor (a n)) + k).toNat
        ≤ (Work.Analysis.EndVar.logN (Nat.floor (a m)) + k).toNat
    have hx : (((Work.Analysis.EndVar.logN (Nat.floor (a n)) + k).toNat : ℕ) : ℤ)
        = Work.Analysis.EndVar.logN (Nat.floor (a n)) + k := Int.toNat_of_nonneg h3
    have hy : (((Work.Analysis.EndVar.logN (Nat.floor (a m)) + k).toNat : ℕ) : ℤ)
        = Work.Analysis.EndVar.logN (Nat.floor (a m)) + k := Int.toNat_of_nonneg h4
    have h5 : (((Work.Analysis.EndVar.logN (Nat.floor (a n)) + k).toNat : ℕ) : ℤ)
        ≤ (((Work.Analysis.EndVar.logN (Nat.floor (a m)) + k).toNat : ℕ) : ℤ) := by
      rw [hx, hy]; omega
    exact_mod_cast h5
  have hσcoe : ∀ n : ℕ, ((σ n : ℕ) : ℤ) = Work.Analysis.EndVar.logN (Nat.floor (a n)) + k := by
    intro n
    rw [hσdef]
    exact Int.toNat_of_nonneg (by have h := hk n; omega)
  -- the pointwise transfer of the variational norm along the reindexing
  have hpoint : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₁
          (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0) f x)
      ≤ PointwiseErgodicTheorems.variationalNorm r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x) := by
    intro x
    have hfun : (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₁
          (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0) f x)
        = fun n : ℕ => (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x) (σ n) := by
      funext n
      rw [Work.KMTAreas.A7.Tle_varphiN_zero]
      show Work.KMTContract.kmtProj ρ l₁ (-(Work.Analysis.EndVar.logN (Nat.floor (a n)))) f x
        = Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + ((σ n : ℕ) : ℤ))) f x
      have h1 : (-(Work.Analysis.EndVar.logN (Nat.floor (a n))) : ℤ)
          = -((m₀ : ℤ) + ((σ n : ℕ) : ℤ)) := by
        rw [hm₀, hσcoe n]
        ring
      rw [h1]
    rw [hfun]
    exact Work.KMTAreas.A7.variationalNorm_comp_mono_le
      (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x) hσmono
  have hdyad : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2) *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    simpa only [Work.KMTAreas.A7Hi.lpf] using hmain l₁ m₀ f hgood'
  refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => by
    simpa only [enorm_eq_self] using hpoint x)).trans hdyad

end

end Work.KMTPlan.A6
