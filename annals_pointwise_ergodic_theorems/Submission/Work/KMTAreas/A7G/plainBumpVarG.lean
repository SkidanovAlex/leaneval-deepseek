/-
# The arithmetic-free (`l₂ = 0`) low-pass variational estimate for the `g`-side bumps

This module proves `Work.KMTAreas.A7G.plainBumpVarG`, the `l₂ = 0`, `k₂ = 0` case of the paper's
(lin-2) (Krause–Mirek–Tao, Annals 195 (2022), §8) for the `g`-side Ionescu–Wainger bumps
`φ̃_N = varphitildeN d N 0`:

  `‖ V^r_n (Tle ρ 0 (varphitildeN d ⌊a n⌋ 0) g) ‖_{ℓ^p} ≤ C ‖g‖_{ℓ^p}`,

uniformly in the `Λ`-lacunary family `a` and in `g` (the constant may depend on `d, Λ, r, p`).

## The route

* `Tle ρ 0 φ = convOp (cw φ)` (`Work.KMTAreas.A7Hi.Tle_zero_eq_convOp_cw`), and the coefficients of
  the bump are the *dilates of the single fixed profile* `kmtPhi = 𝓕 kmtEta`:
  `cw (varphitildeN d N 0) j = (1/σ)·kmtPhi(j/σ)`, `σ = bumpScale d N := 2^{d·logN N}`
  (`cw_etaCut_eq_dilateG`).
* Hence `Tle ρ 0 (varphitildeN d N 0) g = bumpKer σ g` with
  `bumpKer σ g x = Σ'_j (1/σ)·K(j/σ)·g(x-j)`, `K := PsiS` (`Work.KMTPlan.Bile.Defs`) — exactly the
  kernel form of `Work.KMTAreas.A7Hi.DilVar`, the Jones–Seeger–Wright/Lépingle low-pass estimate
  for a fixed Schwartz bump (PROVED, axiom-clean).
* `DilVar` requires a **`2`-lacunary** scale family, while a `Λ`-lacunary one is only monotone.
  But the scales `2^{d·logN ⌊a n⌋}` take their values in the `2`-lacunary family `k ↦ 2^{L₀+k}`
  (`L₀ := d·logN ⌊a 0⌋`), and reading a family along a monotone index map does not increase its
  variational norm (`Work.KMTAreas.A7.variationalNorm_comp_mono_le`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.Tle_varphitildeNt_bounded
import Submission.Work.KMTAreas.A7.cwEtaCutDefs
import Submission.Work.KMTAreas.A7.LoHelpers
import Submission.Work.KMTAreas.A7Hi.DilVar
import Submission.Work.KMTAreas.A7Hi.Tle_zero_eq_convOp_cw
import Submission.Work.KMTPlan.Bile.Defs
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7G

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.KMTContract Work.Analysis.EndVar
open Work.KMTPlan.Bile

/-- The scale of the `g`-side bump `varphitildeN d N 0`: a power of two, `2^{d·logN N}`. -/
noncomputable def bumpScale (d N : ℕ) : ℕ := 2 ^ (d * (Work.Analysis.EndVar.logN N).toNat)

/-- The low-pass family at the integer scale `σ` in the kernel form of `Work.KMTAreas.A7Hi.DilVar`
(with the fixed Schwartz profile `PsiS = 𝓕 kmtEta`). -/
noncomputable def bumpKer (σ : ℕ) (g : ℤ → ℂ) : ℤ → ℂ :=
  fun x => ∑' j : ℤ,
    (1 / ((σ : ℝ) : ℂ)) * Work.KMTPlan.Bile.PsiS ((j : ℝ) / (σ : ℝ)) * g (x - j)

/-! ## §1.  `varphitildeN d N 0` is the rescaled KMT cutoff, and its coefficients -/

/-- The bottom-scale `g`-side bump is the rescaled KMT cutoff of level `-(d · logN N)`. -/
theorem varphitildeN_zero_eq_etaCutG (d N : ℕ) :
    Work.KMTAreas.A7.varphitildeN d N 0
      = Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
          (-((d : ℤ) * Work.Analysis.EndVar.logN N)) := by
  have hpow : ((((d : ℤ) * Work.Analysis.EndVar.logN N : ℤ)) : ℝ)
      = (d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ) := by
    push_cast
    ring
  funext ξ
  simp only [Work.KMTAreas.A7.varphitildeN, if_true, Work.Analysis.IonescuWainger.etaCut]
  rw [← hpow, Real.rpow_intCast,
    show (2 : ℝ) ^ (-((d : ℤ) * Work.Analysis.EndVar.logN N))
        = ((2 : ℝ) ^ (((d : ℤ) * Work.Analysis.EndVar.logN N)))⁻¹ from by rw [zpow_neg]]
  rw [div_inv_eq_mul]
  congr 1
  ring

/-- **The dilation identity for the coefficients of the rescaled KMT cutoff**:
`cw η_{≤k} j = 2^k · φ(2^k j)` with `φ = 𝓕 η = kmtPhi`. -/
theorem cw_etaCut_eq_dilateG (k : ℤ) (j : ℤ) :
    Work.KMTAreas.A7.cw
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) j
      = (((2 : ℝ) ^ k : ℝ) : ℂ) * Work.KMTAreas.A7.kmtPhi ((2 : ℝ) ^ k * (j : ℝ)) := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  rw [Work.KMTAreas.A7.cw_eq_fourierTransform]
  change FourierTransform.fourier
        (fun θ : ℝ => Work.KMTContract.kmtEta (θ / (2 : ℝ) ^ k)) (j : ℝ)
      = (((2 : ℝ) ^ k : ℝ) : ℂ) * FourierTransform.fourier Work.KMTContract.kmtEta
          ((2 : ℝ) ^ k * (j : ℝ))
  rw [Commons.Analysis.Fourier.fourier_comp_div Work.KMTContract.kmtEta hpos (j : ℝ)]
  rw [show ((j : ℝ) * (2 : ℝ) ^ k) = (2 : ℝ) ^ k * (j : ℝ) from mul_comm _ _]

/-- **The coefficients of the bump are the dilates of the fixed profile `kmtPhi`.** -/
theorem cw_varphitildeN_eq_dilateG (d N : ℕ) (j : ℤ) :
    Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphitildeN d N 0) j
      = (1 / ((bumpScale d N : ℝ) : ℂ))
          * Work.KMTPlan.Bile.PsiS ((j : ℝ) / (bumpScale d N : ℝ)) := by
  have hlog : (0 : ℤ) ≤ Work.Analysis.EndVar.logN N := by
    unfold Work.Analysis.EndVar.logN
    exact Int.natCast_nonneg _
  have hL : (((d * (Work.Analysis.EndVar.logN N).toNat : ℕ)) : ℤ)
      = (d : ℤ) * Work.Analysis.EndVar.logN N := by
    push_cast
    rw [Int.toNat_of_nonneg hlog]
  have hσR : ((bumpScale d N : ℕ) : ℝ) = (2 : ℝ) ^ (d * (Work.Analysis.EndVar.logN N).toNat) := by
    rw [bumpScale]
    push_cast
    ring
  have hscal : (((2 : ℝ) ^ (-((d : ℤ) * Work.Analysis.EndVar.logN N)) : ℝ) : ℂ)
      = 1 / ((bumpScale d N : ℝ) : ℂ) := by
    rw [← hL, zpow_neg, zpow_natCast, hσR, one_div]
    push_cast
    ring
  have hargR : ((2 : ℝ) ^ (-((d : ℤ) * Work.Analysis.EndVar.logN N)) * (j : ℝ))
      = (j : ℝ) / (bumpScale d N : ℝ) := by
    rw [← hL, zpow_neg, zpow_natCast, hσR]
    rw [div_eq_mul_inv, mul_comm]
  rw [varphitildeN_zero_eq_etaCutG, cw_etaCut_eq_dilateG, hscal, hargR]
  rw [show Work.KMTAreas.A7.kmtPhi ((j : ℝ) / (bumpScale d N : ℝ))
      = Work.KMTPlan.Bile.PsiS ((j : ℝ) / (bumpScale d N : ℝ)) from
    (Work.KMTPlan.Bile.Psi_apply _).trans rfl]

/-- **The `l₂ = 0` operator as a convolution with the dilates of `kmtPhi`.** -/
theorem Tle_zero_eq_kernelFormG (d N : ℕ) (ρ : ℝ) (g : ℤ → ℂ) :
    Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphitildeN d N 0) g
      = bumpKer (bumpScale d N) g := by
  funext x
  rw [Work.KMTAreas.A7Hi.Tle_zero_eq_convOp_cw
    (φ := Work.KMTAreas.A7.varphitildeN d N 0)
    (Work.KMTAreas.A7.integrable_varphitildeN_aux d N 0) ρ]
  simp only [Work.KMTAreas.A7.convOp, bumpKer]
  exact tsum_congr (fun j => by rw [cw_varphitildeN_eq_dilateG])

/-! ## §2.  The estimate -/

/-- **The `l₂ = 0` low-pass variational estimate for the `g`-side bumps.** -/
theorem plainBumpVarG (d : ℕ) (hd : 1 ≤ d) (ρ : ℝ) (Λ : NNReal) (hΛ : 1 < Λ) (r : NNReal)
    (hr : 2 < r) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
      (ha1 : ∀ n, 1 ≤ a n) (g : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0
          (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a n)) 0) g x))
        p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm g p MeasureTheory.Measure.count := by
  have hpR : (1 : ℝ) < p.toReal :=
    (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hptop.ne).mpr hp
  obtain ⟨C, hCpos, hDil⟩ := Work.KMTAreas.A7Hi.DilVar p.toReal hpR r hr Work.KMTPlan.Bile.PsiS
  refine ⟨C, hCpos, fun a ha ha1 g => ?_⟩
  have hmono_a : Monotone a := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
    have h2 : Λ < a (n + 1) / a n := ha n
    have h1 : Λ * a n < a (n + 1) := by rwa [lt_div_iff₀ hpos] at h2
    have h3 : a n ≤ Λ * a n := by
      simpa using mul_le_mul_of_nonneg_right (le_of_lt hΛ) (le_of_lt hpos)
    exact le_trans h3 h1.le
  set L₀ : ℕ := d * (Work.Analysis.EndVar.logN (Nat.floor (a 0))).toNat with hL₀
  set sig : ℕ → ℕ := fun k => 2 ^ (L₀ + k) with hsig
  set lev : ℕ → ℕ := fun n => d * (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat - L₀
    with hlev
  have hlevmono : Monotone lev := by
    intro n m hnm
    refine Nat.sub_le_sub_right ?_ L₀
    refine Nat.mul_le_mul_left d (Int.toNat_le_toNat ?_)
    exact Work.Analysis.EndVar.logN_mono (Nat.floor_mono (hmono_a hnm))
  have hsig1 : ∀ k : ℕ, 1 ≤ sig k := by
    intro k; rw [hsig]; exact Nat.one_le_two_pow
  have hsig2 : ∀ k : ℕ, 2 * sig k ≤ sig (k + 1) := by
    intro k
    have hk : sig k = 2 ^ (L₀ + k) := congrFun hsig k
    have hk1 : sig (k + 1) = 2 ^ (L₀ + (k + 1)) := congrFun hsig (k + 1)
    rw [hk, hk1]
    have heq : 2 ^ (L₀ + (k + 1)) = 2 * 2 ^ (L₀ + k) := by
      rw [show L₀ + (k + 1) = (L₀ + k) + 1 from by omega, pow_succ]
      ring
    rw [heq]
  have hle : ∀ n : ℕ, L₀ ≤ d * (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat := by
    intro n
    rw [hL₀]
    exact Nat.mul_le_mul_left d (Int.toNat_le_toNat
      (Work.Analysis.EndVar.logN_mono (Nat.floor_mono (hmono_a (Nat.zero_le n)))))
  have hlevel : ∀ n : ℕ, d * (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat
      = L₀ + lev n := by
    intro n
    show d * (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat
      = L₀ + (d * (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat - L₀)
    have hn := hle n
    omega
  have hsiglev : ∀ n : ℕ, sig (lev n)
      = 2 ^ (d * (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat) := by
    intro n
    show 2 ^ (L₀ + lev n) = 2 ^ (d * (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat)
    rw [← hlevel n]
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0
          (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a n)) 0) g x)
      ≤ PointwiseErgodicTheorems.variationalNorm r (fun k : ℕ => bumpKer (sig k) g x) := by
    intro x
    have h1 : (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0
          (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a n)) 0) g x)
        = (fun n : ℕ => (fun k : ℕ => bumpKer (sig k) g x) (lev n)) := by
      funext n
      rw [Tle_zero_eq_kernelFormG]
      show bumpKer (2 ^ (d * (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat)) g x
        = bumpKer (sig (lev n)) g x
      rw [hsiglev n]
    rw [h1]
    exact Work.KMTAreas.A7.variationalNorm_comp_mono_le (fun k : ℕ => bumpKer (sig k) g x) hlevmono
  have hmain := hDil sig hsig1 hsig2 g
  rw [ENNReal.ofReal_toReal hptop.ne] at hmain
  refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm)
    (f := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0
        (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a n)) 0) g x))
    (g := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
      (fun k : ℕ => bumpKer (sig k) g x))
    (fun x => by
      rw [enorm_eq_self, enorm_eq_self]
      exact hpt x)).trans ?_
  simpa only [bumpKer] using hmain

end

end Work.KMTAreas.A7G
