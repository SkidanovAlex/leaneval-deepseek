
/-
# The Fourier mass of the KMT bumps (`bumpFourierMass`)

This module proves `Work.KMTPlan.A6.bumpFourierMass`: the `ℓ¹(ℤ)`-mass of the Fourier transform
of the Ionescu--Wainger bumps `varphiN N k₁`, `varphitildeN d N k₂` along a lattice translate of
the real line is `≲ 1 + 2^{k₁}/N` (resp. `≲ 1 + 2^{d k₂}/N^d`).

## The mechanism

`varphiN N k₁` (for `k₁ ≥ 1`) is the fixed bump `lacψ = η - η(2·)` dilated to the frequency scale
`lacσ N k₁ = 2^{Log N - k₁}` (`bfm_varphiN_pos`), while `varphitildeN d N k₂` (for `k₂ ≥ 1`) is the
`d`-scaled bump `bfmBump d = η - η(2^d ·)` dilated to `bfmTildeScale d N k₂ = 2^{d(Log N - k₂)}`
(`bfm_varphitildeN_pos`); at the bottom height the bumps are the single dilations
`η (2^{Log N} ·)`, `η (2^{d Log N} ·)`.  Since the inverse Fourier transform scales as
`𝓕⁻ (m (c ·)) x = c⁻¹ 𝓕⁻ m (x / c)` (`Work.KMTAreas.A7.fourierInv_comp_mul`), and since such a
`𝓕⁻ m` decays like `(1 + |y|)^{-2}` (`FourierDecayExplicit`), the mass sum is bounded by

  `sup_y (1 + |y|²) ‖𝓕⁻ m y‖ · ∑_n c / (c + |u - n|)²`,

and the lattice sum is `≲ 1 + 1/c` (`latticeQuadMass`, proved in
`Submission/Work/KMTPlan/A6/latticeQuadMass.lean`).  The arithmetic `1/c ≲ 2^{k}/N` completes the
proof.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.bfmDefs
import Submission.Work.KMTPlan.A6.latticeQuadMass
import Submission.Work.KMTAreas.A7.FourierDecayExplicit

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators FourierTransform
open Work.Analysis.IonescuWainger
open Work.KMTContract

/-! ## The inverse Fourier transform as an integral -/

/-- **The inverse Fourier transform is the integral against the character `ee`.**  With
`ee x = e^{2πix}` one has `∫ θ, F θ * ee (x θ) = 𝓕⁻ F x` for every `F : ℝ → ℂ` (the integral is
the Bochner integral against Lebesgue measure). -/
theorem bfm_integral_eq_fourierInv (F : ℝ → ℂ) (x : ℝ) :
    (∫ θ : ℝ, F θ * Work.KMTAreas.A7.ee (x * θ))
      = FourierTransformInv.fourierInv F x := by
  rw [Work.KMTAreas.A7.fourierInv_eq_real]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  beta_reduce
  rw [Circle.smul_def, smul_eq_mul, ← Work.KMTAreas.A7.ee_eq_fourierChar (θ * x)]
  rw [show x * θ = θ * x by ring]
  ring

/-- `‖(r : ℂ)‖ = r` for `r ≥ 0`. -/
theorem bfm_norm_ofReal_nonneg {r : ℝ} (h : 0 ≤ r) : ‖((r : ℝ) : ℂ)‖ = r := by
  have h1 : ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, sq]
  rw [← Real.sqrt_sq (norm_nonneg _), h1, Real.sqrt_sq_eq_abs, abs_of_nonneg h]

/-! ## Quadratic decay of the inverse Fourier transform -/

/-- **Quadratic decay of `𝓕⁻ m` for a `C²` compactly supported `m`** (the inverse-transform
counterpart of `Work.KMTAreas.A7.FourierDecayExplicit`, obtained from it by
`𝓕⁻ m y = 𝓕 m (-y)`). -/
theorem bfm_fourierInv_decay (m : ℝ → ℂ) (hcd : ContDiff ℝ 2 m) (hcs : HasCompactSupport m) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ,
      ‖FourierTransformInv.fourierInv m y‖ ≤ C / (1 + |y|) ^ 2 := by
  refine ⟨4 * max (∫ y, ‖m y‖) (∫ y, ‖iteratedDeriv 2 m y‖) + 1, ?_, fun y => ?_⟩
  · have h1 : (0 : ℝ) ≤ ∫ y, ‖m y‖ := integral_nonneg fun y => norm_nonneg _
    have h2 : (0 : ℝ) ≤ max (∫ y, ‖m y‖) (∫ y, ‖iteratedDeriv 2 m y‖) :=
      le_max_of_le_left h1
    linarith
  · rw [Real.fourierInv_eq_fourier_neg]
    simpa using Work.KMTAreas.A7.FourierDecayExplicit hcd hcs (-y)

theorem bfm_decay_kmtEta : ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ,
    ‖FourierTransformInv.fourierInv kmtEta y‖ ≤ C / (1 + |y|) ^ 2 :=
  bfm_fourierInv_decay kmtEta (bfm_contDiff_kmtEta 2) bfm_hasCompactSupport_kmtEta

theorem bfm_decay_bfmBump (d : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ,
    ‖FourierTransformInv.fourierInv (bfmBump d) y‖ ≤ C / (1 + |y|) ^ 2 :=
  bfm_fourierInv_decay (bfmBump d) (contDiff_bfmBump d) (hasCompactSupport_bfmBump d)

theorem bfm_decay_lacψ : ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ,
    ‖FourierTransformInv.fourierInv Work.KMTAreas.A7.lacψ y‖ ≤ C / (1 + |y|) ^ 2 := by
  obtain ⟨C, hC, h⟩ := bfm_decay_bfmBump 1
  exact ⟨C, hC, fun y => by rw [← bfmBump_one]; exact h y⟩

/-! ## The bumps are dilations of a fixed bump -/

theorem bfm_varphiN_zero (N : ℕ) :
    Work.KMTAreas.A7.varphiN N 0
      = fun ξ => kmtEta ((2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) * ξ) := by
  funext ξ
  simp only [Work.KMTAreas.A7.varphiN, if_true]

theorem bfm_varphiN_pos (N k : ℕ) (hk : 1 ≤ k) :
    Work.KMTAreas.A7.varphiN N k
      = fun ξ => Work.KMTAreas.A7.lacψ (Work.KMTAreas.A7.lacσ N k * ξ) := by
  funext ξ
  have hk' : ¬ (k = 0) := by omega
  simp only [Work.KMTAreas.A7.varphiN, if_neg hk', Work.KMTAreas.A7.lacψ,
    Work.KMTAreas.A7.lacσ_eq N k]
  rw [show (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)
      = (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) * 2 by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]]
  rw [show (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) * 2 * ξ
      = 2 * ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) * ξ) by ring]

theorem bfm_varphitildeN_zero (d N : ℕ) :
    Work.KMTAreas.A7.varphitildeN d N 0
      = fun ξ => kmtEta ((2 : ℝ) ^ ((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) * ξ) := by
  funext ξ
  simp only [Work.KMTAreas.A7.varphitildeN, if_true]

theorem bfm_varphitildeN_pos (d N k : ℕ) (hk : 1 ≤ k) :
    Work.KMTAreas.A7.varphitildeN d N k
      = fun ξ => bfmBump d (bfmTildeScale d N k * ξ) := by
  funext ξ
  have hk' : ¬ (k = 0) := by omega
  simp only [Work.KMTAreas.A7.varphitildeN, if_neg hk', bfmBump, bfmTildeScale]
  have hexp : (d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)
      = (d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) + (d : ℝ) := by ring
  rw [hexp, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
  rw [show (2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * (2 : ℝ) ^ d * ξ
      = (2 : ℝ) ^ d * ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * ξ)
      by ring]

/-! ## The arithmetic of the dilating scales -/

/-- `2 ^ Log N ≥ N / 2`. -/
theorem bfm_two_mul_pow_logN (N : ℕ) :
    (N : ℝ) ≤ 2 * (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) := by
  have h : max N 2 < 2 ^ (Nat.log 2 (max N 2) + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) (max N 2)
  have hcast : ((max N 2 : ℕ) : ℝ) < (((2 : ℕ) ^ (Nat.log 2 (max N 2) + 1) : ℕ) : ℝ) := by
    exact_mod_cast h
  have h2 : (((2 : ℕ) ^ (Nat.log 2 (max N 2) + 1) : ℕ) : ℝ)
      = 2 * (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) := by
    rw [Work.Analysis.EndVar.logN]
    push_cast
    rw [pow_succ]
    push_cast
    rw [Real.rpow_natCast]
    ring
  rw [h2] at hcast
  exact le_trans (by exact_mod_cast le_max_left N 2) (le_of_lt hcast)

/-- `1 / 2 ^ Log N ≤ 2 / N` for `N ≥ 1`. -/
theorem bfm_inv_pow_logN_le {N : ℕ} (hN : 1 ≤ N) :
    1 / (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) ≤ 2 / (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hP : (0 : ℝ) < (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hhalf : (N : ℝ) / 2 ≤ (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) := by
    have := bfm_two_mul_pow_logN N
    linarith
  have hN2 : (0 : ℝ) < (N : ℝ) / 2 := by linarith
  calc 1 / (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ)
      ≤ 1 / ((N : ℝ) / 2) := one_div_le_one_div_of_le hN2 hhalf
    _ = 2 / (N : ℝ) := by field_simp

/-- The scale `lacσ N k = 2 ^ (Log N - k)` is at least `N / (2 · 2^k)`. -/
theorem bfm_lacσ_ge {N k : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) / (2 * (2 : ℝ) ^ k) ≤ Work.KMTAreas.A7.lacσ N k := by
  rw [Work.KMTAreas.A7.lacσ_eq N k]
  rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  rw [← Real.rpow_natCast (2 : ℝ) k]
  have hL : (N : ℝ) / 2 ≤ (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) := by
    have := bfm_two_mul_pow_logN N
    linarith
  have hpk : (0 : ℝ) < (2 : ℝ) ^ (k : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have h2pk : (0 : ℝ) < 2 * (2 : ℝ) ^ (k : ℝ) := by linarith
  rw [div_le_div_iff₀ h2pk hpk]
  nlinarith [hL, hpk]

/-- `1 / lacσ N k ≤ 2 · 2^k / N` for `N ≥ 1`. -/
theorem bfm_inv_lacσ_le {N k : ℕ} (hN : 1 ≤ N) :
    1 / Work.KMTAreas.A7.lacσ N k ≤ 2 * (2 : ℝ) ^ k / (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < (N : ℝ) / (2 * (2 : ℝ) ^ k) := by positivity
  calc 1 / Work.KMTAreas.A7.lacσ N k ≤ 1 / ((N : ℝ) / (2 * (2 : ℝ) ^ k)) :=
        one_div_le_one_div_of_le hpos (bfm_lacσ_ge hN)
    _ = 2 * (2 : ℝ) ^ k / (N : ℝ) := by field_simp

/-- `1 / (2 ^ (d Log N)) ≤ 2^d / N^d`. -/
theorem bfm_inv_etaScale_le {d N : ℕ} (hN : 1 ≤ N) :
    1 / (2 : ℝ) ^ ((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ))
      ≤ (2 : ℝ) ^ d / (N : ℝ) ^ d := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have heq : ((2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ)) ^ d
      = (2 : ℝ) ^ ((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ)) d]
    rw [← Real.rpow_mul (show (0 : ℝ) ≤ 2 by norm_num)]
    congr 1
    ring
  rw [← heq, one_div, ← inv_pow]
  have hinv := bfm_inv_pow_logN_le hN
  rw [one_div] at hinv
  calc (((2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ))⁻¹) ^ d
      ≤ (2 / (N : ℝ)) ^ d := pow_le_pow_left₀ (by positivity) hinv d
    _ = (2 : ℝ) ^ d / (N : ℝ) ^ d := by rw [div_pow]

/-- `bfmTildeScale d N k = (lacσ N k)^d`. -/
theorem bfm_tildeScale_eq (d N k : ℕ) :
    bfmTildeScale d N k = (Work.KMTAreas.A7.lacσ N k) ^ d := by
  rw [bfmTildeScale, Work.KMTAreas.A7.lacσ_eq N k]
  rw [← Real.rpow_natCast ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) d]
  rw [← Real.rpow_mul (show (0 : ℝ) ≤ 2 by norm_num)]
  congr 1
  ring

/-- `1 / bfmTildeScale d N k ≤ 2^d 2^{dk} / N^d`. -/
theorem bfm_inv_tildeScale_le {d N k : ℕ} (hN : 1 ≤ N) :
    1 / bfmTildeScale d N k ≤ (2 : ℝ) ^ d * (2 : ℝ) ^ (d * k) / (N : ℝ) ^ d := by
  rw [bfm_tildeScale_eq d N k, one_div, ← inv_pow]
  have hinv := bfm_inv_lacσ_le (N := N) (k := k) hN
  rw [one_div] at hinv
  have h0 : (0 : ℝ) ≤ (Work.KMTAreas.A7.lacσ N k)⁻¹ :=
    (inv_pos.mpr (Work.KMTAreas.A7.lacσ_pos N k)).le
  calc ((Work.KMTAreas.A7.lacσ N k)⁻¹) ^ d
      ≤ (2 * (2 : ℝ) ^ k / (N : ℝ)) ^ d := pow_le_pow_left₀ h0 hinv d
    _ = (2 : ℝ) ^ d * (2 : ℝ) ^ (d * k) / (N : ℝ) ^ d := by
        rw [div_pow, mul_pow, ← pow_mul, Nat.mul_comm k d]

/-! ## The mass bound -/

/-- **The `ℓ¹(ℤ)` mass of a dilated decaying symbol.**  If `‖𝓕⁻ m y‖ ≤ C (1+|y|)^{-2}` then the
lattice samples of the inverse transform of the dilated symbol `m (b ·)` satisfy
`∑_n ‖𝓕⁻ (m (b ·)) (u - n)‖ ≤ C · (4 (1 + 1/b))`. -/
theorem bfm_tsum_mass {g : ℝ → ℂ} {C b : ℝ} (hb : 0 < b)
    (hdec : ∀ y : ℝ, ‖g y‖ ≤ C / (1 + |y|) ^ 2) (u : ℝ) :
    (∑' n : ℤ, ‖(b : ℂ)⁻¹ * g ((u - (n : ℝ)) / b)‖) ≤ C * (4 * (1 + 1 / b)) := by
  have hC : (0 : ℝ) ≤ C := by
    have h := hdec 0
    simpa using le_trans (norm_nonneg (g 0)) h
  obtain ⟨hsum, hbound⟩ := latticeQuadMass b hb u
  have hstep : ∀ n : ℤ, ‖(b : ℂ)⁻¹ * g ((u - (n : ℝ)) / b)‖
      ≤ C * (b / (b + |u - (n : ℝ)|) ^ 2) := by
    intro n
    have hA : (1 + |u - (n : ℝ)| / b) ^ 2 = (b + |u - (n : ℝ)|) ^ 2 / b ^ 2 := by
      rw [eq_div_iff (by positivity : (b ^ 2 : ℝ) ≠ 0)]
      field_simp
    have hB : b⁻¹ * (C / ((b + |u - (n : ℝ)|) ^ 2 / b ^ 2))
        = C * (b / (b + |u - (n : ℝ)|) ^ 2) := by
      field_simp
    have hdec' : ‖g ((u - (n : ℝ)) / b)‖ ≤ C / (1 + |u - (n : ℝ)| / b) ^ 2 := by
      have habs : |(u - (n : ℝ)) / b| = |u - (n : ℝ)| / b := by rw [abs_div, abs_of_pos hb]
      simpa only [habs] using hdec ((u - (n : ℝ)) / b)
    calc ‖(b : ℂ)⁻¹ * g ((u - (n : ℝ)) / b)‖
        = b⁻¹ * ‖g ((u - (n : ℝ)) / b)‖ := by
          rw [norm_mul, norm_inv, bfm_norm_ofReal_nonneg hb.le]
      _ ≤ b⁻¹ * (C / (1 + |u - (n : ℝ)| / b) ^ 2) :=
          mul_le_mul_of_nonneg_left hdec' (by positivity)
      _ = b⁻¹ * (C / ((b + |u - (n : ℝ)|) ^ 2 / b ^ 2)) := by rw [hA]
      _ = C * (b / (b + |u - (n : ℝ)|) ^ 2) := hB
  have hmaj : Summable fun n : ℤ => C * (b / (b + |u - (n : ℝ)|) ^ 2) := hsum.mul_left C
  refine le_trans (Summable.tsum_le_tsum hstep ?_ hmaj) ?_
  · exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) hstep hmaj
  · rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hbound hC

/-- **The mass of the bumps in dilation form.**  For `c > 0` and a symbol `m` with quadratic decay
of `𝓕⁻ m`, the mass sum of the dilated symbol `θ ↦ m (c θ)` is `≤ C (4 (1 + 1/c))`. -/
theorem bfm_mass_dilated {m : ℝ → ℂ} {C c : ℝ} (hc : 0 < c)
    (hdec : ∀ y : ℝ, ‖FourierTransformInv.fourierInv m y‖ ≤ C / (1 + |y|) ^ 2) (u : ℝ) :
    (∑' p : ℤ, ‖∫ θ : ℝ, m (c * θ) * Work.KMTAreas.A7.ee ((u - (p : ℝ)) * θ)‖)
      ≤ C * (4 * (1 + 1 / c)) := by
  have h1 : ∀ p : ℤ,
      (∫ θ : ℝ, m (c * θ) * Work.KMTAreas.A7.ee ((u - (p : ℝ)) * θ))
        = (c : ℂ)⁻¹ * FourierTransformInv.fourierInv m ((u - (p : ℝ)) / c) := by
    intro p
    rw [bfm_integral_eq_fourierInv]
    exact congrFun (Work.KMTAreas.A7.fourierInv_comp_mul m hc) (u - (p : ℝ))
  calc (∑' p : ℤ, ‖∫ θ : ℝ, m (c * θ) * Work.KMTAreas.A7.ee ((u - (p : ℝ)) * θ)‖)
      = ∑' p : ℤ, ‖(c : ℂ)⁻¹ * FourierTransformInv.fourierInv m ((u - (p : ℝ)) / c)‖ :=
        tsum_congr fun p => congrArg norm (h1 p)
    _ ≤ C * (4 * (1 + 1 / c)) := bfm_tsum_mass hc hdec u

/-! ## Elementary arithmetic of the final constants -/

/-- `4 (1 + x) ≤ 8 (1 + y)` when `x ≤ 2 y`. -/
theorem bfm_four_le_eight {x y : ℝ} (h : x ≤ 2 * y) : 4 * (1 + x) ≤ 8 * (1 + y) := by linarith

/-- The comparison `C (4 (1 + x)) ≤ C' (1 + y)` for the bottom heights: `x ≤ 2 y`, `8 C ≤ C'`. -/
theorem bfm_mass_le {C C' x y : ℝ} (hC : 0 ≤ C) (h8 : 8 * C ≤ C') (hx : x ≤ 2 * y)
    (hy : 0 ≤ y) : C * (4 * (1 + x)) ≤ C' * (1 + y) := by
  have h1 : 4 * (1 + x) ≤ 8 * (1 + y) := bfm_four_le_eight hx
  have h2 : (0 : ℝ) ≤ 1 + y := by linarith
  calc C * (4 * (1 + x)) ≤ C * (8 * (1 + y)) := mul_le_mul_of_nonneg_left h1 hC
    _ = (8 * C) * (1 + y) := by ring
    _ ≤ C' * (1 + y) := mul_le_mul_of_nonneg_right h8 h2

/-- The comparison `C (4 (1 + x)) ≤ C' (1 + y)` for the rescaled heights: `x ≤ a y`,
`4 C (1 + a) ≤ C'`. -/
theorem bfm_mass_le_mul {C C' a x y : ℝ} (hC : 0 ≤ C) (h4 : 4 * C * (1 + a) ≤ C')
    (ha : 0 ≤ a) (hy : 0 ≤ y) (hx : x ≤ a * y) :
    C * (4 * (1 + x)) ≤ C' * (1 + y) := by
  have h1 : 4 * (1 + x) ≤ 4 * (1 + a) * (1 + y) := by nlinarith
  have h2 : (0 : ℝ) ≤ 1 + y := by linarith
  calc C * (4 * (1 + x)) ≤ C * (4 * (1 + a) * (1 + y)) := mul_le_mul_of_nonneg_left h1 hC
    _ = (4 * C * (1 + a)) * (1 + y) := by ring
    _ ≤ C' * (1 + y) := mul_le_mul_of_nonneg_right h4 h2

/-! ## The main theorem -/

theorem bumpFourierMass (P : Polynomial ℤ) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (N k₁ : ℕ), 1 ≤ N → ∀ u : ℝ,
        (∑' p : ℤ, ‖∫ θ : ℝ,
            Work.KMTAreas.A7.varphiN N k₁ θ * Work.KMTAreas.A7.ee ((u - (p : ℝ)) * θ)‖)
          ≤ C * (1 + (2 : ℝ) ^ k₁ / (N : ℝ))) ∧
      (∀ (N k₂ : ℕ), 1 ≤ N → ∀ u : ℝ,
        (∑' p : ℤ, ‖∫ θ : ℝ,
            Work.KMTAreas.A7.varphitildeN (P.natDegree) N k₂ θ
              * Work.KMTAreas.A7.ee ((u - (p : ℝ)) * θ)‖)
          ≤ C * (1 + (2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ (P.natDegree))) := by
  obtain ⟨Cη, hCηpos, hCη⟩ := bfm_decay_kmtEta
  obtain ⟨Cψ, hCψpos, hCψ⟩ := bfm_decay_lacψ
  obtain ⟨Cd, hCdpos, hCd⟩ := bfm_decay_bfmBump P.natDegree
  have hCη0 : (0 : ℝ) ≤ Cη := hCηpos.le
  have hCψ0 : (0 : ℝ) ≤ Cψ := hCψpos.le
  have hCd0 : (0 : ℝ) ≤ Cd := hCdpos.le
  have hZ : (0 : ℝ) ≤ (2 : ℝ) ^ P.natDegree := by positivity
  refine ⟨8 * (Cη + Cψ + Cd) * (1 + (2 : ℝ) ^ P.natDegree) + 1, by positivity, ?_, ?_⟩
  · intro N k₁ hN u
    rcases Nat.eq_zero_or_pos k₁ with hk | hk
    · subst hk
      rw [bfm_varphiN_zero N, pow_zero]
      have hPpos : (0 : ℝ) < (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) :=
        Real.rpow_pos_of_pos (by norm_num) _
      refine le_trans (bfm_mass_dilated (m := kmtEta) hPpos hCη u) ?_
      have hstep : 4 * (1 + 1 / (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ))
          ≤ 8 * (1 + 1 / (N : ℝ)) := by
        have h := bfm_inv_pow_logN_le (N := N) hN
        have he : (2 : ℝ) / (N : ℝ) = 2 * (1 / (N : ℝ)) := by ring
        have h2 : 1 / (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) ≤ 2 * (1 / (N : ℝ)) := by
          linarith [h, he.le, he.ge]
        have h3 : 4 * (1 / (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ))
            ≤ 8 * (1 / (N : ℝ)) := by
          calc 4 * (1 / (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ))
              ≤ 4 * (2 * (1 / (N : ℝ))) := mul_le_mul_of_nonneg_left h2 (by norm_num)
            _ = 8 * (1 / (N : ℝ)) := by ring
        calc 4 * (1 + 1 / (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ))
            = 4 + 4 * (1 / (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ)) := by ring
          _ ≤ 8 + 8 * (1 / (N : ℝ)) := by linarith
          _ = 8 * (1 + 1 / (N : ℝ)) := by ring
      have h8 : 8 * Cη ≤ 8 * (Cη + Cψ + Cd) * (1 + (2 : ℝ) ^ P.natDegree) + 1 := by
        nlinarith [hCη0, hCψ0, hCd0, hZ]
      calc Cη * (4 * (1 + 1 / (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ)))
          ≤ Cη * (8 * (1 + 1 / (N : ℝ))) := mul_le_mul_of_nonneg_left hstep hCη0
        _ = (8 * Cη) * (1 + 1 / (N : ℝ)) := by ring
        _ ≤ (8 * (Cη + Cψ + Cd) * (1 + (2 : ℝ) ^ P.natDegree) + 1) * (1 + 1 / (N : ℝ)) :=
            mul_le_mul_of_nonneg_right h8 (by positivity)
    · rw [bfm_varphiN_pos N k₁ hk]
      have hσpos : (0 : ℝ) < Work.KMTAreas.A7.lacσ N k₁ := Work.KMTAreas.A7.lacσ_pos N k₁
      refine le_trans (bfm_mass_dilated (m := Work.KMTAreas.A7.lacψ) hσpos hCψ u) ?_
      have hstep : 4 * (1 + 1 / Work.KMTAreas.A7.lacσ N k₁)
          ≤ 8 * (1 + (2 : ℝ) ^ k₁ / (N : ℝ)) := by
        have h := bfm_inv_lacσ_le (N := N) (k := k₁) hN
        have h2 : 2 * (2 : ℝ) ^ k₁ / (N : ℝ) = 2 * ((2 : ℝ) ^ k₁ / (N : ℝ)) := by ring
        linarith
      have h8 : 8 * Cψ ≤ 8 * (Cη + Cψ + Cd) * (1 + (2 : ℝ) ^ P.natDegree) + 1 := by
        nlinarith [hCη0, hCψ0, hCd0, hZ]
      calc Cψ * (4 * (1 + 1 / Work.KMTAreas.A7.lacσ N k₁))
          ≤ Cψ * (8 * (1 + (2 : ℝ) ^ k₁ / (N : ℝ))) := mul_le_mul_of_nonneg_left hstep hCψ0
        _ = (8 * Cψ) * (1 + (2 : ℝ) ^ k₁ / (N : ℝ)) := by ring
        _ ≤ (8 * (Cη + Cψ + Cd) * (1 + (2 : ℝ) ^ P.natDegree) + 1)
              * (1 + (2 : ℝ) ^ k₁ / (N : ℝ)) := mul_le_mul_of_nonneg_right h8 (by positivity)
  · intro N k₂ hN u
    rcases Nat.eq_zero_or_pos k₂ with hk | hk
    · subst hk
      rw [bfm_varphitildeN_zero P.natDegree N, mul_zero, pow_zero]
      have hBpos : (0 : ℝ) < (2 : ℝ) ^ ((P.natDegree : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) :=
        Real.rpow_pos_of_pos (by norm_num) _
      refine le_trans (bfm_mass_dilated (m := kmtEta) hBpos hCη u) ?_
      have hstep : 4 * (1 + 1 / (2 : ℝ) ^ ((P.natDegree : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)))
          ≤ 4 * (1 + (2 : ℝ) ^ P.natDegree) * (1 + 1 / (N : ℝ) ^ P.natDegree) := by
        have h := bfm_inv_etaScale_le (d := P.natDegree) (N := N) hN
        have h2 : (2 : ℝ) ^ P.natDegree / (N : ℝ) ^ P.natDegree
            = (2 : ℝ) ^ P.natDegree * (1 / (N : ℝ) ^ P.natDegree) := by ring
        have hy : (0 : ℝ) ≤ 1 / (N : ℝ) ^ P.natDegree := by positivity
        nlinarith [h, hZ, hy, h2.le, h2.ge]
      have h4 : 4 * Cη * (1 + (2 : ℝ) ^ P.natDegree)
          ≤ 8 * (Cη + Cψ + Cd) * (1 + (2 : ℝ) ^ P.natDegree) + 1 := by
        nlinarith [hCη0, hCψ0, hCd0, hZ]
      calc Cη * (4 * (1 + 1 / (2 : ℝ) ^ ((P.natDegree : ℝ) * (Work.Analysis.EndVar.logN N : ℝ))))
          ≤ Cη * (4 * (1 + (2 : ℝ) ^ P.natDegree) * (1 + 1 / (N : ℝ) ^ P.natDegree)) :=
            mul_le_mul_of_nonneg_left hstep hCη0
        _ = (4 * Cη * (1 + (2 : ℝ) ^ P.natDegree)) * (1 + 1 / (N : ℝ) ^ P.natDegree) := by ring
        _ ≤ (8 * (Cη + Cψ + Cd) * (1 + (2 : ℝ) ^ P.natDegree) + 1)
              * (1 + 1 / (N : ℝ) ^ P.natDegree) := mul_le_mul_of_nonneg_right h4 (by positivity)
    · rw [bfm_varphitildeN_pos P.natDegree N k₂ hk]
      have hBpos : (0 : ℝ) < bfmTildeScale P.natDegree N k₂ := by
        rw [bfmTildeScale]
        exact Real.rpow_pos_of_pos (by norm_num) _
      refine le_trans (bfm_mass_dilated (m := bfmBump P.natDegree) hBpos hCd u) ?_
      have hstep : 4 * (1 + 1 / bfmTildeScale P.natDegree N k₂)
          ≤ 4 * (1 + (2 : ℝ) ^ P.natDegree)
              * (1 + (2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree) := by
        have h := bfm_inv_tildeScale_le (d := P.natDegree) (N := N) (k := k₂) hN
        have h2 : (2 : ℝ) ^ P.natDegree * (2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree
            = (2 : ℝ) ^ P.natDegree
              * ((2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree) := by ring
        have hy : (0 : ℝ) ≤ (2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree := by positivity
        nlinarith [h, hZ, hy, h2.le, h2.ge]
      have h4 : 4 * Cd * (1 + (2 : ℝ) ^ P.natDegree)
          ≤ 8 * (Cη + Cψ + Cd) * (1 + (2 : ℝ) ^ P.natDegree) + 1 := by
        nlinarith [hCη0, hCψ0, hCd0, hZ]
      calc Cd * (4 * (1 + 1 / bfmTildeScale P.natDegree N k₂))
          ≤ Cd * (4 * (1 + (2 : ℝ) ^ P.natDegree)
              * (1 + (2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree)) :=
            mul_le_mul_of_nonneg_left hstep hCd0
        _ = (4 * Cd * (1 + (2 : ℝ) ^ P.natDegree))
              * (1 + (2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree) := by ring
        _ ≤ (8 * (Cη + Cψ + Cd) * (1 + (2 : ℝ) ^ P.natDegree) + 1)
              * (1 + (2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree) :=
            mul_le_mul_of_nonneg_right h4 (by positivity)

end

end Work.KMTPlan.A6
