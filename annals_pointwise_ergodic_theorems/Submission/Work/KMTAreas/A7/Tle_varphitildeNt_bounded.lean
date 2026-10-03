/-
# Pointwise boundedness of the Ionescu--Wainger projection of the modulated bump `φ̃_{N,t}`

This file proves `Work.KMTAreas.A7.Tle_varphitildeNt_bounded`: for a bounded sequence `g` on `ℤ`,
the values of the Ionescu--Wainger projection
`Tle ρ l (varphitildeNt P P.natDegree N k t) g` are bounded by a constant *uniformly* in
`t ∈ [1/2, 1]` and `y ∈ ℤ` (with the constant depending on `P, ρ, l, N, k, g, Cg`).

## Proof

`Tle ρ l φ g = iwConv (iwArithFreqs ρ l) (periodize φ) g` is the convolution with the kernel
`κ_j = iwKernel (iwSymbolSet (iwArithFreqs ρ l) (periodize φ)) j`.  Since `g` is only assumed
bounded, the pointwise bound is exactly the statement that `κ` is in `ℓ¹(ℤ)`, i.e. that the
symbol is smooth enough for its Fourier coefficients to decay.

* `Work.KMTPlan.A6.IwKernelArithChar` factors `κ_j` as
  `arithChar ρ l (-j) · cw φ j` (`|arithChar ρ l (-j)| ≤ |(ℚ/ℤ)_{≤l}|`), and
  `Work.KMTAreas.A7.cw_eq_fourierTransform` identifies `cw φ j` with the continuous Fourier
  transform `𝓕 φ j`;
* `𝓕 φ_t = 𝓕 (φ̃_N · e(c_t ·)) = 𝓕 φ̃_N (· - c_t)` by the modulation rule (`fourier_mul_ee`),
  with `c_t = PevalR P (N t)`;
* `Work.KMTAreas.A7.fourierDecay_varphitildeN` gives `‖𝓕 φ̃_N x‖ ≤ Cf / (1 + |x|)^2`;
* `c_t` is bounded uniformly in `t ∈ [1/2,1]` by the coefficient bound `abs_PevalR_mul_le`, and
  `one_div_sq_le_of_abs_sub_le` converts the decay at the shifted frequency `j - c_t` into
  decay at `j` with a `t`-independent constant:
  `‖κ_j‖ ≤ |(ℚ/ℤ)_{≤l}| · Cf · (2M+1)^2 / (1 + |j|)^2`, where `M ≥ |c_t|`;
* the resulting `ℓ¹` bound `∑_j ‖κ_j‖ ≤ |(ℚ/ℤ)_{≤l}| Cf (2M+1)^2 ∑_j 1/(1+|j|)^2` and the
  triangle inequality for the `tsum` finish the proof (`norm_tsum_kernel_mul_le`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.fourierDecay_varphitildeN
import Submission.Work.KMTAreas.A7.abs_PevalR_mul_le
import Submission.Work.KMTAreas.A7.one_div_sq_le_of_abs_sub_le
import Submission.Work.KMTPlan.A6.IwKernelArithChar

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators FourierTransform
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-! ## §1.  The modulation `ee` and the Fourier transform of the modulated bump -/

/-- The modulations multiply: `e(a) · e(b) = e(a + b)` for `e(x) = exp (2 π i x)`. -/
lemma ee_add_ (a b : ℝ) : ee a * ee b = ee (a + b) := by
  simp only [ee, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The modulation has modulus one. -/
lemma norm_ee_ (r : ℝ) : ‖ee r‖ = 1 := by
  rw [ee, show (2 : ℂ) * ↑Real.pi * Complex.I * ↑r = ↑(2 * Real.pi * r) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- **The modulation rule for the Fourier transform.**  Multiplying a function by the modulation
`ξ ↦ e(c ξ)` shifts its Fourier transform by `c`.  (As both sides are integrals this holds
unconditionally.) -/
lemma fourier_mul_ee (f : ℝ → ℂ) (c x : ℝ) :
    FourierTransform.fourier (fun ξ => f ξ * ee (c * ξ)) x
      = FourierTransform.fourier f (x - c) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [smul_eq_mul, ee]
  set E1 := Complex.exp (↑(-2 * Real.pi * a * x) * Complex.I) with hE1
  set E2 := Complex.exp (2 * ↑Real.pi * Complex.I * ↑(c * a)) with hE2
  set E3 := Complex.exp (↑(-2 * Real.pi * a * (x - c)) * Complex.I) with hE3
  have h : E1 * E2 = E3 := by
    rw [hE1, hE2, hE3, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc E1 * (f a * E2) = (E1 * E2) * f a := by ring
    _ = E3 * f a := by rw [h]

/-- The Fourier transform of the modulated bump is the shifted Fourier transform of the
unmodulated bump. -/
lemma fourier_varphitildeNt_eq (P : Polynomial ℤ) (d N k : ℕ) (t x : ℝ) :
    FourierTransform.fourier (varphitildeNt P d N k t) x
      = FourierTransform.fourier (varphitildeN d N k) (x - PevalR P ((N : ℝ) * t)) := by
  rw [show varphitildeNt P d N k t
      = fun ξ : ℝ => varphitildeN d N k ξ * ee (PevalR P ((N : ℝ) * t) * ξ) from rfl]
  exact fourier_mul_ee _ _ _

/-! ## §2.  Integrability of the bumps -/

/-- The rescaled cutoff `η_{≤0} = η` is the cutoff itself. -/
lemma etaCut_kmtEta_zero' :
    etaCut Work.KMTContract.kmtEta (0 : ℤ) = Work.KMTContract.kmtEta := by
  funext θ
  simp [etaCut]

/-- The cutoff `η` has compact support. -/
lemma hasCompactSupport_kmtEta_ : HasCompactSupport Work.KMTContract.kmtEta := by
  have h := Work.KMTAreas.A7.hasCompactSupport_etaCut (0 : ℤ)
  rwa [etaCut_kmtEta_zero'] at h

/-- The cutoff `η` is integrable. -/
lemma integrable_kmtEta_ : Integrable Work.KMTContract.kmtEta :=
  contDiff_kmtEta_top.continuous.integrable_of_hasCompactSupport hasCompactSupport_kmtEta_

/-- The rescaled bump `φ̃_N` is integrable. -/
lemma integrable_varphitildeN_aux (d N k : ℕ) :
    Integrable (varphitildeN d N k) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hbase : ∀ a : ℝ, a ≠ 0 → Integrable (fun ξ : ℝ => Work.KMTContract.kmtEta (a * ξ)) :=
    fun a ha => integrable_kmtEta_.comp_mul_left' ha
  unfold varphitildeN
  split_ifs with hk
  · exact hbase _ (ne_of_gt (Real.rpow_pos_of_pos h2 _))
  · exact (hbase _ (ne_of_gt (Real.rpow_pos_of_pos h2 _))).sub
      (hbase _ (ne_of_gt (Real.rpow_pos_of_pos h2 _)))

/-- The modulated bump `φ̃_{N,t}` is integrable (the modulation has modulus one). -/
lemma integrable_varphitildeNt_aux (P : Polynomial ℤ) (d N k : ℕ) (t : ℝ) :
    Integrable (varphitildeNt P d N k t) := by
  have hcont : Continuous (fun ξ : ℝ => ee (PevalR P ((N : ℝ) * t) * ξ)) := by
    unfold ee
    fun_prop
  have h := (integrable_varphitildeN_aux d N k).bdd_mul hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ξ => le_of_eq (norm_ee_ _)))
  have hswap : Integrable (fun ξ : ℝ =>
      varphitildeN d N k ξ * ee (PevalR P ((N : ℝ) * t) * ξ)) :=
    h.congr (Filter.Eventually.of_forall (fun ξ => by ring))
  exact hswap.congr (Filter.Eventually.of_forall (fun ξ => rfl))

/-! ## §3.  The Ionescu--Wainger kernel of the modulated bump -/

/-- **The kernel identity.**  The `j`-th Fourier coefficient of the IW symbol of the modulated
bump is the arithmetic character `arithChar ρ l (-j) = ∑_{α ∈ (ℚ/ℤ)_{≤l}} e(-j α)` times the
Fourier transform of the unmodulated bump at the shifted frequency `j - c_t`,
`c_t = PevalR P (N t)`. -/
lemma iwKernel_varphitildeNt_eq (P : Polynomial ℤ) (ρ : ℝ) (l d N k : ℕ) (t : ℝ) (j : ℤ) :
    iwKernel (iwSymbolSet (iwArithFreqs ρ l) (periodize (varphitildeNt P d N k t))) j
      = arithChar ρ l (-j)
        * FourierTransform.fourier (varphitildeN d N k) ((j : ℝ) - PevalR P ((N : ℝ) * t)) := by
  have hid := Work.KMTPlan.A6.IwKernelArithChar (iwArithFreqs ρ l)
    (integrable_varphitildeNt_aux P d N k t) j
  rw [hid, cw_eq_fourierTransform]
  change (∑ α ∈ iwArithFreqs ρ l, fourier (T := 1) (-j) α)
        * FourierTransform.fourier (varphitildeNt P d N k t) (j : ℝ)
      = (∑ α ∈ iwArithFreqs ρ l, fourier (T := 1) (-j) α)
        * FourierTransform.fourier (varphitildeN d N k) ((j : ℝ) - PevalR P ((N : ℝ) * t))
  rw [show FourierTransform.fourier (varphitildeNt P d N k t) (j : ℝ)
      = FourierTransform.fourier (varphitildeN d N k) ((j : ℝ) - PevalR P ((N : ℝ) * t)) from
    fourier_varphitildeNt_eq P d N k t (j : ℝ)]

/-- The modulus of the arithmetic character is bounded by the number of arithmetic frequencies. -/
lemma norm_arithChar_le_ (ρ : ℝ) (l : ℕ) (y : ℤ) :
    ‖arithChar ρ l y‖ ≤ ((iwArithFreqs ρ l).card : ℝ) := by
  rw [arithChar]
  calc ‖∑ α ∈ iwArithFreqs ρ l, fourier (T := 1) y α‖
      ≤ ∑ α ∈ iwArithFreqs ρ l, ‖fourier (T := 1) y α‖ := norm_sum_le _ _
    _ = ∑ _α ∈ iwArithFreqs ρ l, (1 : ℝ) := by
        refine Finset.sum_congr rfl (fun α _ => ?_)
        rw [fourier_apply]
        exact _root_.Circle.norm_coe _
    _ = ((iwArithFreqs ρ l).card : ℝ) := by simp

/-! ## §4.  The `ℓ¹` bound for the kernel -/

/-- `∑_j 1/(1+|j|)^2 < ∞` on `ℤ`. -/
lemma summable_one_div_sq_int : Summable (fun j : ℤ => 1 / (1 + |(j : ℝ)|) ^ 2) := by
  have hdec : ∀ j : ℤ,
      ‖(((1 / (1 + |(j : ℝ)|) ^ 2 : ℝ)) : ℂ)‖ ≤ (1 : ℝ) / (1 + |(j : ℝ)|) ^ 2 := by
    intro j
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := Work.KMTContract.kernel_l1_of_decay
    (c := fun j : ℤ => (((1 / (1 + |(j : ℝ)|) ^ 2 : ℝ)) : ℂ)) (C := 1) hdec
  have h' : (fun j : ℤ => ‖(((1 / (1 + |(j : ℝ)|) ^ 2 : ℝ)) : ℂ)‖)
      = fun j : ℤ => 1 / (1 + |(j : ℝ)|) ^ 2 := by
    funext j
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rwa [h'] at h

/-- A bounded sequence times an `ℓ¹` kernel is summable. -/
lemma summable_mul_of_bounded_ {κ z : ℤ → ℂ} {B : ℝ}
    (hκ : Summable fun j : ℤ => ‖κ j‖) (hz : ∀ j : ℤ, ‖z j‖ ≤ B) :
    Summable fun j : ℤ => κ j * z j := by
  refine Summable.of_norm_bounded (hκ.mul_left (max B 0)) (fun j => ?_)
  rw [norm_mul]
  calc ‖κ j‖ * ‖z j‖ ≤ ‖κ j‖ * max B 0 :=
        mul_le_mul_of_nonneg_left ((hz j).trans (le_max_left B 0)) (norm_nonneg _)
    _ = max B 0 * ‖κ j‖ := by ring

/-- **The `ℓ¹` kernel bound for the IW convolution.**  If the kernel `j ↦ iwKernel (iwSymbolSet A Φ) j`
decays like `Cκ / (1 + |j|)^2` and `v` is bounded by `B`, then the convolution at any point is
bounded by `Cκ * (∑_j 1/(1+|j|)^2) * max B 0`. -/
lemma norm_tsum_kernel_mul_le {A : Finset Work.Analysis.IonescuWainger.Circle}
    {Φ : Work.Analysis.IonescuWainger.Circle → ℂ} {v : ℤ → ℂ} {Cκ B : ℝ}
    (hdec : ∀ j : ℤ, ‖iwKernel (iwSymbolSet A Φ) j‖ ≤ Cκ / (1 + |(j : ℝ)|) ^ 2)
    (hB : ∀ m : ℤ, ‖v m‖ ≤ B) (n : ℤ) :
    ‖∑' j : ℤ, iwKernel (iwSymbolSet A Φ) j * v (n - j)‖
      ≤ Cκ * (∑' j : ℤ, 1 / (1 + |(j : ℝ)|) ^ 2) * max B 0 := by
  have hκ : Summable fun j : ℤ => ‖iwKernel (iwSymbolSet A Φ) j‖ :=
    Work.KMTContract.kernel_l1_of_decay hdec
  have hz : ∀ j : ℤ, ‖v (n - j)‖ ≤ max B 0 := fun j => (hB _).trans (le_max_left B 0)
  have hs : Summable fun j : ℤ => iwKernel (iwSymbolSet A Φ) j * v (n - j) :=
    summable_mul_of_bounded_ hκ hz
  have hbase : Summable fun j : ℤ => 1 / (1 + |(j : ℝ)|) ^ 2 := summable_one_div_sq_int
  calc ‖∑' j : ℤ, iwKernel (iwSymbolSet A Φ) j * v (n - j)‖
      ≤ ∑' j : ℤ, ‖iwKernel (iwSymbolSet A Φ) j * v (n - j)‖ := norm_tsum_le_tsum_norm hs.norm
    _ = ∑' j : ℤ, ‖iwKernel (iwSymbolSet A Φ) j‖ * ‖v (n - j)‖ := by
        refine tsum_congr fun j => ?_
        rw [norm_mul]
    _ ≤ ∑' j : ℤ, ‖iwKernel (iwSymbolSet A Φ) j‖ * max B 0 :=
        Summable.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left (hz j) (norm_nonneg _))
          (by simpa only [norm_mul] using hs.norm) (hκ.mul_right (max B 0))
    _ = (∑' j : ℤ, ‖iwKernel (iwSymbolSet A Φ) j‖) * max B 0 := tsum_mul_right
    _ ≤ (Cκ * (∑' j : ℤ, 1 / (1 + |(j : ℝ)|) ^ 2)) * max B 0 := by
        refine mul_le_mul_of_nonneg_right ?_ (le_max_right B 0)
        calc (∑' j : ℤ, ‖iwKernel (iwSymbolSet A Φ) j‖)
            ≤ ∑' j : ℤ, Cκ * (1 / (1 + |(j : ℝ)|) ^ 2) := by
              refine Summable.tsum_le_tsum (fun j => ?_) hκ (hbase.mul_left Cκ)
              have h3 := hdec j
              rw [div_eq_mul_one_div] at h3
              exact h3
          _ = Cκ * (∑' j : ℤ, 1 / (1 + |(j : ℝ)|) ^ 2) := tsum_mul_left

/-! ## §5.  The target -/

/-- **The pointwise bound for the IW projection of the modulated bump.**  For a bounded sequence
`g`, the values of `Tle ρ l (varphitildeNt P P.natDegree N k t) g` are bounded by a constant
which is uniform in `t ∈ [1/2, 1]` and in the point `y ∈ ℤ`. -/
theorem Tle_varphitildeNt_bounded (P : Polynomial ℤ) (ρ : ℝ) (l : ℕ) (N k : ℕ) (g : ℤ → ℂ) (Cg : ℝ)
    (hg : ∀ y : ℤ, ‖g y‖ ≤ Cg) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ y : ℤ,
      ‖Work.KMTAreas.A7.Tle ρ l (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t) g y‖ ≤ C := by
  classical
  obtain ⟨Cf, hCfpos, hCfdec⟩ := fourierDecay_varphitildeN P.natDegree N k
  set Mv : ℝ := max 1 ((∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|) *
    (1 + (N : ℝ)) ^ P.natDegree) with hMv
  set S : ℝ := ∑' j : ℤ, 1 / (1 + |(j : ℝ)|) ^ 2 with hS
  set K : ℝ := (2 * Mv + 1) ^ 2 with hK
  have hMnonneg : 0 ≤ Mv := le_trans zero_le_one (le_max_left 1 _)
  have hKpos : 0 < K := by rw [hK]; positivity
  refine ⟨((iwArithFreqs ρ l).card : ℝ) * Cf * K * S * max Cg 0, ?_⟩
  intro t ht y
  have ht1 : |t| ≤ 1 := by
    obtain ⟨h1, h2⟩ := ht
    rw [abs_le]
    exact ⟨by linarith, h2⟩
  have hc : |PevalR P ((N : ℝ) * t)| ≤ Mv :=
    le_trans (abs_PevalR_mul_le P N ht1) (le_max_right 1 _)
  -- the decay of the kernel at this `t`
  have hdec : ∀ j : ℤ,
      ‖iwKernel (iwSymbolSet (iwArithFreqs ρ l)
        (periodize (varphitildeNt P P.natDegree N k t))) j‖
        ≤ (((iwArithFreqs ρ l).card : ℝ) * Cf * K) / (1 + |(j : ℝ)|) ^ 2 := by
    intro j
    rw [iwKernel_varphitildeNt_eq P ρ l P.natDegree N k t j]
    have h1 : ‖arithChar ρ l (-j)‖ ≤ ((iwArithFreqs ρ l).card : ℝ) := norm_arithChar_le_ ρ l (-j)
    have h2 : ‖FourierTransform.fourier (varphitildeN P.natDegree N k)
          ((j : ℝ) - PevalR P ((N : ℝ) * t))‖ ≤ Cf * K / (1 + |(j : ℝ)|) ^ 2 := by
      refine le_trans (hCfdec ((j : ℝ) - PevalR P ((N : ℝ) * t))) ?_
      have hmaj := one_div_sq_le_of_abs_sub_le hMnonneg hc j
      have hKeq : K = (2 * Mv + 1) ^ 2 := hK
      calc Cf / (1 + |(j : ℝ) - PevalR P ((N : ℝ) * t)|) ^ 2
          = Cf * (1 / (1 + |(j : ℝ) - PevalR P ((N : ℝ) * t)|) ^ 2) := div_eq_mul_one_div _ _
        _ ≤ Cf * (K / (1 + |(j : ℝ)|) ^ 2) := by
            refine mul_le_mul_of_nonneg_left ?_ hCfpos.le
            rw [hKeq]
            exact hmaj
        _ = Cf * K / (1 + |(j : ℝ)|) ^ 2 := (mul_div_assoc _ _ _).symm
    calc ‖arithChar ρ l (-j) *
            FourierTransform.fourier (varphitildeN P.natDegree N k)
              ((j : ℝ) - PevalR P ((N : ℝ) * t))‖
        = ‖arithChar ρ l (-j)‖ *
            ‖FourierTransform.fourier (varphitildeN P.natDegree N k)
              ((j : ℝ) - PevalR P ((N : ℝ) * t))‖ := norm_mul _ _
      _ ≤ ((iwArithFreqs ρ l).card : ℝ) * (Cf * K / (1 + |(j : ℝ)|) ^ 2) :=
          mul_le_mul h1 h2 (norm_nonneg _) (Nat.cast_nonneg _)
      _ = ((iwArithFreqs ρ l).card : ℝ) * Cf * K / (1 + |(j : ℝ)|) ^ 2 := by ring
  rw [Tle_apply]
  refine le_trans (norm_tsum_kernel_mul_le hdec (fun m => hg m) y) ?_
  rw [hS]

end

end Work.KMTAreas.A7
