/-
# The bottom-height unmodulated low-pass lacunary variational estimate

The unmodulated family `n ↦ Tle ρ 0 (varphiN ⌊a n⌋ 0)` is, at arithmetic height `0`, the family of
bump dilations `bumpOp K₀ (2^{logN ⌊a n⌋})` (`Work.KMTAreas.A7LoLin.kmtProj_zero_eq_bumpOp`), and
the dyadic levels `n ↦ logN ⌊a n⌋` are monotone.  Hence the estimate follows from Lépingle's
inequality for lacunary bump dilations (`Work.KMTAreas.A7LoLin.lacunaryBumpDilationVarK`) by
monotone reindexing (`Work.KMTAreas.A7.variationalNorm_comp_mono_le`).

The main lemma below is stated with the Lépingle bound as an explicit hypothesis, so that it is
independent of the (large) Lépingle chain.
-/
import Mathlib
import Submission.Work.KMTAreas.A7LoLin.kernel0
import Submission.Work.KMTAreas.A7.LoHelpers
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.KMTAreas.A7LoLin

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.KMTAreas.A7
open Work.Analysis.EndVar

noncomputable section

/-- `varphiN N 0 = etaCut η (-(logN N))`. -/
theorem varphiN_zero_eq_etaCut_aux (N : ℕ) :
    varphiN N 0 = Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(logN N)) := by
  funext ξ
  simp only [varphiN, if_true, Work.Analysis.IonescuWainger.etaCut]
  congr 1
  rw [div_eq_mul_inv, zpow_neg, inv_inv, Real.rpow_intCast]
  ring

/-- `Tle ρ l (varphiN N 0) = kmtProj ρ l (-(logN N))`. -/
theorem Tle_varphiN_zero_aux (ρ : ℝ) (l : ℕ) (N : ℕ) :
    Work.KMTAreas.A7.Tle ρ l (varphiN N 0) = Work.KMTContract.kmtProj ρ l (-(logN N)) := by
  rw [varphiN_zero_eq_etaCut_aux]
  exact Work.KMTAreas.A7.Tle_etaCut ρ l (-(logN N))

/-- `logN` is monotone. -/
theorem logN_mono_aux {N M : ℕ} (h : N ≤ M) : logN N ≤ logN M := by
  simp only [logN, Int.ofNat_le]
  exact Nat.log_mono_right (by omega)

/-- The map `n ↦ logN ⌊a n⌋` is monotone. -/
theorem logN_floor_mono {Λ : NNReal} (hΛ : 1 < Λ) {a : ℕ → NNReal}
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) :
    Monotone (fun n : ℕ => logN (Nat.floor (a n))) := by
  have hmonoA : Monotone a := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
    have h2 : Λ < a (n + 1) / a n := ha n
    have h1 : Λ * a n < a (n + 1) := by rwa [lt_div_iff₀ hpos] at h2
    have h3 : a n ≤ Λ * a n := by
      simpa using mul_le_mul_of_nonneg_right (le_of_lt hΛ) (le_of_lt hpos)
    exact le_trans h3 h1.le
  exact fun m n hmn => logN_mono_aux (Nat.floor_mono (hmonoA hmn))

/-- The dyadic level map `n ↦ logN ⌊a n⌋` is monotone. -/
theorem lev_mono {Λ : NNReal} (hΛ : 1 < Λ) {a : ℕ → NNReal}
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) :
    Monotone (fun n : ℕ => (logN (Nat.floor (a n))).toNat) := by
  have hmonoA : Monotone a := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
    have h2 : Λ < a (n + 1) / a n := ha n
    have h1 : Λ * a n < a (n + 1) := by rwa [lt_div_iff₀ hpos] at h2
    have h3 : a n ≤ Λ * a n := by
      simpa using mul_le_mul_of_nonneg_right (le_of_lt hΛ) (le_of_lt hpos)
    exact le_trans h3 h1.le
  intro m n hmn
  have h1 : logN (Nat.floor (a m)) ≤ logN (Nat.floor (a n)) :=
    logN_mono_aux (Nat.floor_mono (hmonoA hmn))
  have h2 : (0 : ℤ) ≤ logN (Nat.floor (a m)) := by simp only [logN]; positivity
  exact Int.toNat_le_toNat h1

/-- **The bottom-height unmodulated low-pass estimate**, from Lépingle's inequality. -/
theorem lowpass0_of_lepingle (ρ : ℝ) {Λ : NNReal} (hΛ : 1 < Λ) (p : ℝ) (hp : 1 < p) (r : NNReal)
    (hr : 2 < r)
    (hLep : ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℕ → ℕ), (∀ n, 1 ≤ σ n) →
      (∀ n, 2 * σ n ≤ σ (n + 1)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => ∑' j : ℤ, (1 / (σ n : ℝ)) * K0 ((j : ℝ) / (σ n)) * f (x - j)))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            MeasureTheory.Measure.count) :
    ∃ C : NNReal, ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
      (ha1 : ∀ n, 1 ≤ a n) (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0 (varphiN (Nat.floor (a n)) 0) f x))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ (C : ENNReal) * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            MeasureTheory.Measure.count := by
  obtain ⟨C, hCpos, hLep'⟩ := hLep
  refine ⟨⟨C, hCpos.le⟩, ?_⟩
  intro a ha ha1 f
  classical
  have hlev : Monotone (fun n : ℕ => (logN (Nat.floor (a n))).toNat) := lev_mono hΛ ha ha1
  have hstep : ∀ n : ℕ, (fun x : ℤ => Work.KMTAreas.A7.Tle ρ 0 (varphiN (Nat.floor (a n)) 0) f x)
      = (fun x : ℤ => Work.KMTAreas.A7.bumpOp K0 (fun k => 2 ^ k)
          ((logN (Nat.floor (a n))).toNat) f x) := by
    intro n
    funext x
    rw [Tle_varphiN_zero_aux ρ 0 (Nat.floor (a n))]
    rw [show (-(logN (Nat.floor (a n))) : ℤ)
        = -(((logN (Nat.floor (a n))).toNat : ℕ) : ℤ) from by
      rw [Int.toNat_of_nonneg (by simp only [logN]; positivity)]]
    exact congrFun (kmtProj_zero_eq_bumpOp_zero ρ ((logN (Nat.floor (a n))).toNat) f) x
  have hpt : ∀ x : ℤ,
      PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          Work.KMTAreas.A7.Tle ρ 0 (varphiN (Nat.floor (a n)) 0) f x)
        ≤ PointwiseErgodicTheorems.variationalNorm r (fun m : ℕ =>
            Work.KMTAreas.A7.bumpOp K0 (fun k => 2 ^ k) m f x) := by
    intro x
    have h1 : (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0 (varphiN (Nat.floor (a n)) 0) f x)
        = fun n : ℕ => (fun m : ℕ => Work.KMTAreas.A7.bumpOp K0 (fun k => 2 ^ k) m f x)
            ((fun n : ℕ => (logN (Nat.floor (a n))).toNat) n) := by
      funext n
      exact congrFun (hstep n) x
    rw [h1]
    exact variationalNorm_comp_mono_le
      (fun m : ℕ => Work.KMTAreas.A7.bumpOp K0 (fun k => 2 ^ k) m f x) hlev
  refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (f := fun x : ℤ =>
      PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
        Work.KMTAreas.A7.Tle ρ 0 (varphiN (Nat.floor (a n)) 0) f x))
    (g := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun m : ℕ =>
      Work.KMTAreas.A7.bumpOp K0 (fun k => 2 ^ k) m f x))
    (fun x => by rw [enorm_eq_self, enorm_eq_self]; exact hpt x)).trans ?_
  have hσ1 : ∀ m : ℕ, 1 ≤ (fun k => 2 ^ k : ℕ → ℕ) m := fun m => Nat.one_le_two_pow
  have hσ2 : ∀ m : ℕ, 2 * (fun k => 2 ^ k : ℕ → ℕ) m ≤ (fun k => 2 ^ k : ℕ → ℕ) (m + 1) := by
    intro m
    simp only
    rw [pow_succ]
    omega
  have hmain := hLep' (fun k => 2 ^ k) hσ1 hσ2 f
  refine hmain.trans (le_of_eq ?_)
  exact congrArg (fun t : ENNReal => t * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
      MeasureTheory.Measure.count) (ENNReal.ofReal_coe_nnreal (p := ⟨C, hCpos.le⟩))

end

end Work.KMTAreas.A7LoLin
