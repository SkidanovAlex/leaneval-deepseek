/-
# The uniform bound on the symbol of the linearised deviation kernel

`Work.KMTAreas.A7.LoDevSymBound`: for a Schwartz kernel `K` there is a constant `C` such that for
*every* `2`-lacunary scale sequence `σ` (with `1 ≤ σ n`), every finite index set `U`, every sign
pattern `ω` and every frequency `θ`,

  `‖∑'_j lacDevLin K σ U ω j · e^{2πi j θ}‖ ≤ C`.

`lacDevLin` is the signed sum `∑_{n ∈ U} ω_n · devKern K σ n` of the deviation kernels
`devKern K σ n j = (1/σ n) K (j/σ n) − (∫K) · triKernel (lacLev σ n) j`, so the claim is the uniform
`ℓ^∞` bound for the symbol of the linearised deviation family — the Littlewood–Paley input of the
square-function half of the lacunary bump-dilation variational estimate.

The proof has three parts.

* **The symbol identity** (`Work.KMTAreas.A7.lacDevLin_tsum_eq` and
  `Work.KMTAreas.A7.lacDevPerScaleSym`, both already in the library): summing the per-scale Fourier
  series and exchanging the finite `U`-sum with the `j`-sum reduces the left-hand side to the finite
  signed sum `∑_{n ∈ U} bSign ω n · (bumpSym K (σ n) θ − lacConst K · triSym (lacLev σ n) θ)`.

* **The single-scale symbol estimates.**  Write `s = zGap θ = ‖1 − e^{2πiθ}‖` and
  `d = nearDist θ = |θ − ⌊θ + 1/2⌋|`.  Then
  - `‖bumpSym K m θ − lacConst K‖ ≤ A/m² + A·m·d` and `‖bumpSym K m θ‖ ≤ A/m² + A·(1 + m·d)⁻²`
    (`Work.KMTAreas.A7Hi.bumpSymQuad`);
  - `‖1 − triSym L θ‖ ≤ 4·2^L·s` and `s·‖triSym L θ‖ ≤ 5/2^L`
    (`Work.KMTAreas.A7Hi.triSym_sub_one_le_zGap`, `Work.KMTAreas.A7Hi.zGap_mul_triSym_le`);
  - `4 d ≤ s ≤ 2 π d` (`loNearFacts`, proved here);
  - `𝓕K` is Lipschitz at the origin (`loFourierLipschitz`, proved here; it supplies the hypothesis of
    the bump estimate).

  (The three estimates quoted from `Work.KMTAreas.A7Hi` are proved, with no gaps, in
  `Submission/Work/KMTAreas/A7Hi/DilVar.lean`; the two Fejér estimates are the triangular-symbol
  bounds and the bump estimate is the modulated Poisson summation for the sampled kernel.)

* **The lacunary summation.**  Since `σ` is `2`-lacunary, `σ n ≥ 2^n`, so the scale sequence is
  strictly increasing and splitting `U` at the threshold `σ n · s = 1` makes the small-scale part
  contribute `O(σ n · s)` and the large-scale part `O((σ n · s)⁻¹)`:
  `loLacSum` proves `∑_{n ∈ U} min (σ n s) (σ n s)⁻¹ ≤ 4` (the two parts are each bounded by the
  geometric series `∑ 2^{-k} ≤ 2`), and `loSumInvSqScale` proves `∑_{n ∈ U} (σ n)⁻² ≤ 2`.

Summing the termwise bound in the two regimes gives the uniform constant
`C = 2 A + 4 max (A/4 + 8‖∫K‖) (64 A + 10‖∫K‖) + 1`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7Hi.DilVar

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators FourierTransform

noncomputable section

/-! ## The Fourier transform of a Schwartz function is Lipschitz at the origin

`𝓕K` is again a Schwartz function, so its derivative is bounded; the mean value inequality on
`[0, y]` gives `‖𝓕K y − 𝓕K 0‖ ≤ C |y|`. -/

theorem loFourierLipschitz (K : SchwartzMap ℝ ℂ) :
    ∃ L : ℝ, 0 < L ∧ ∀ y : ℝ,
      ‖FourierTransform.fourier (K : ℝ → ℂ) y
        - FourierTransform.fourier (K : ℝ → ℂ) 0‖ ≤ L * |y| := by
  obtain ⟨C, hCpos, hC⟩ :=
    Commons.Analysis.Fourier.schwartz_decay_real
      (SchwartzMap.derivCLM ℝ ℂ (𝓕 K : SchwartzMap ℝ ℂ)) 0
  have hCd : ∀ t : ℝ, ‖deriv (⇑(𝓕 K : SchwartzMap ℝ ℂ)) t‖ ≤ C := by
    intro t
    have h := hC t
    rw [SchwartzMap.derivCLM_apply] at h
    have hexp : (1 + |t|) ^ (-(↑(0 : ℕ) : ℝ)) = 1 := by
      rw [show (-(↑(0 : ℕ) : ℝ)) = 0 by norm_num, Real.rpow_zero]
    rw [hexp, mul_one] at h
    exact h
  refine ⟨C, hCpos, fun y => ?_⟩
  have hmain := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
    (f := ⇑(𝓕 K : SchwartzMap ℝ ℂ))
    (s := Set.uIcc (0 : ℝ) y) (x := 0) (y := y) (C := C)
    (fun z _ => (SchwartzMap.hasDerivAt (𝓕 K : SchwartzMap ℝ ℂ) z).differentiableAt)
    (fun z _ => hCd z)
    (convex_uIcc (0 : ℝ) y) Set.left_mem_uIcc Set.right_mem_uIcc
  rw [sub_zero, Real.norm_eq_abs] at hmain
  exact hmain

/-! ## Elementary facts about `nearInt`, `nearDist` and `zGap` -/

lemma loNearDistLeHalf (θ : ℝ) : nearDist θ ≤ 1 / 2 := by
  have h1 : ((nearInt θ : ℤ) : ℝ) ≤ θ + 1 / 2 := Int.floor_le (θ + 1 / 2)
  have h2 : θ + 1 / 2 < ((nearInt θ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one (θ + 1 / 2)
  rw [nearDist, abs_le]
  constructor <;> linarith

lemma loChrOneEq (θ : ℝ) :
    Work.KMTAreas.ADev.chr 1 θ = Complex.exp (Complex.I * ((2 * Real.pi * θ : ℝ) : ℂ)) := by
  rw [Work.KMTAreas.ADev.chr]
  congr 1
  push_cast
  ring

/-- `zGap θ = 2 |sin (π θ)|`. -/
lemma loZGapEq (θ : ℝ) : zGap θ = 2 * |Real.sin (Real.pi * θ)| := by
  have h := Complex.norm_exp_I_mul_ofReal_sub_one (2 * Real.pi * θ)
  rw [zGap, loChrOneEq, norm_sub_rev, h]
  rw [show (2 * Real.pi * θ) / 2 = Real.pi * θ by ring, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- Shifting by the nearest integer does not change `|sin (π θ)|`. -/
lemma loAbsSinPiEqNearDist (θ : ℝ) :
    |Real.sin (Real.pi * θ)| = |Real.sin (Real.pi * nearDist θ)| := by
  set n₀ : ℤ := nearInt θ with hn₀
  have hd : nearDist θ = |θ - (n₀ : ℝ)| := by rw [nearDist, hn₀]
  have hmain : Real.pi * θ
      = Real.pi * (θ - (n₀ : ℝ)) + ((n₀ : ℤ) : ℝ) * Real.pi := by push_cast; ring
  rw [hmain, Real.sin_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul]
  rw [hd]
  rcases le_or_gt 0 (θ - (n₀ : ℝ)) with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, mul_neg, Real.sin_neg, abs_neg]

/-- **The comparability of `zGap` and `nearDist`.**  `4 d ≤ zGap θ ≤ 2 π d`, `d = nearDist θ`. -/
theorem loNearFacts (θ : ℝ) :
    nearDist θ ≤ 1 / 2 ∧ 4 * nearDist θ ≤ zGap θ ∧ zGap θ ≤ 2 * Real.pi * nearDist θ := by
  have hd := loNearDistLeHalf θ
  have hd0 : 0 ≤ nearDist θ := by rw [nearDist]; positivity
  have hsin := loAbsSinPiEqNearDist θ
  have harg : |Real.pi * nearDist θ| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos, abs_of_nonneg hd0]
    nlinarith [Real.pi_pos, hd]
  refine ⟨hd, ?_, ?_⟩
  · have h := Real.mul_abs_le_abs_sin harg
    have h' : (2 / Real.pi) * (Real.pi * nearDist θ)
        ≤ |Real.sin (Real.pi * nearDist θ)| := by
      have h3 : |Real.pi * nearDist θ| = Real.pi * nearDist θ :=
        abs_of_nonneg (mul_nonneg Real.pi_pos.le hd0)
      rwa [h3] at h
    have h3 : (2 / Real.pi) * (Real.pi * nearDist θ) = 2 * nearDist θ := by
      field_simp
    rw [h3] at h'
    rw [loZGapEq, hsin]
    linarith
  · have h := Real.abs_sin_le_abs (x := Real.pi * nearDist θ)
    rw [loZGapEq, hsin]
    have h' : 2 * |Real.sin (Real.pi * nearDist θ)| ≤ 2 * (Real.pi * nearDist θ) := by
      have h2 : |Real.pi * nearDist θ| = Real.pi * nearDist θ :=
        abs_of_nonneg (mul_nonneg Real.pi_pos.le hd0)
      rw [h2] at h
      linarith
    linarith [h']

/-! ## The lacunary summation

For a `2`-lacunary `σ` and any `s ≥ 0`, splitting the index set `U` at `σ n · s = 1` bounds the
small-scale part by the geometric series `∑ 2^{-k} ≤ 2` and the large-scale part by the same series
(`lacunary_finset_sum_inv_le` with `X = 1`).  Both are supplied by the commons lemmas
`Commons.Analysis.Sum.lacunary_finset_sum_le` and `Commons.Analysis.Sum.lacunary_finset_sum_inv_le`,
applied to the finite set of scales `{σ n : n ∈ U} ⊆ ℝ`. -/

/-- `∑_{n ∈ U} ((σ n : ℝ)^2)⁻¹ ≤ 2` for a `2`-lacunary `σ` with `1 ≤ σ n`. -/
theorem loSumInvSqScale (σ : ℕ → ℕ) (hσ1 : ∀ n, 1 ≤ σ n)
    (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1)) (U : Finset ℕ) :
    ∑ n ∈ U, (((σ n : ℕ) : ℝ) ^ 2)⁻¹ ≤ 2 := by
  refine (Finset.sum_le_sum fun n _ => ?_).trans (sum_inv_scale_le_two σ hσ1 hσ2 U)
  have h1 : (1 : ℝ) ≤ ((σ n : ℕ) : ℝ) := by exact_mod_cast hσ1 n
  have hinv0 : (0 : ℝ) ≤ (((σ n : ℕ) : ℝ))⁻¹ := by positivity
  have hinv1 : (((σ n : ℕ) : ℝ))⁻¹ ≤ 1 := by
    have h := one_div_le_one_div_of_le (a := (1 : ℝ)) (b := ((σ n : ℕ) : ℝ)) one_pos h1
    simpa [one_div] using h
  have hsplit : (((σ n : ℕ) : ℝ) ^ 2)⁻¹
      = (((σ n : ℕ) : ℝ))⁻¹ * (((σ n : ℕ) : ℝ))⁻¹ := by
    rw [pow_two, mul_inv]
  rw [hsplit]
  nlinarith [hinv0, hinv1]

/-- Doubling a `ℕ`-sequence: `2 ^ k * σ m ≤ σ (m + k)`. -/
lemma loTwoPowMulLe {σ : ℕ → ℕ} (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1)) (k m : ℕ) :
    2 ^ k * σ m ≤ σ (m + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc 2 ^ (k + 1) * σ m = 2 * (2 ^ k * σ m) := by rw [pow_succ]; ring
        _ ≤ 2 * σ (m + k) := Nat.mul_le_mul_left 2 ih
        _ ≤ σ (m + k + 1) := hσ2 (m + k)
        _ = σ (m + (k + 1)) := by rw [Nat.add_assoc]

/-- A doubling `ℕ`-sequence with `1 ≤ σ n` is strictly increasing. -/
lemma loStrictMonoSigma {σ : ℕ → ℕ} (hσ1 : ∀ n, 1 ≤ σ n)
    (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1)) : StrictMono σ := by
  intro a b hab
  have hsub : 2 ^ (b - a) * σ a ≤ σ b := by
    have h := loTwoPowMulLe hσ2 (b - a) a
    rwa [Nat.add_sub_cancel' hab.le] at h
  have hk : 1 ≤ b - a := Nat.sub_pos_of_lt hab
  have h2k : 2 ≤ 2 ^ (b - a) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (b - a) := Nat.pow_le_pow_right (by norm_num) hk
  have h1 : 1 ≤ σ a := hσ1 a
  calc σ a < 2 * σ a := by omega
    _ ≤ 2 ^ (b - a) * σ a := Nat.mul_le_mul_right _ h2k
    _ ≤ σ b := hsub

/-- For `0 ≤ t ≤ 1`: `min t t⁻¹ = t`. -/
lemma loMinInvOfLeOne {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : min t t⁻¹ = t := by
  refine min_eq_left ?_
  rcases eq_or_lt_of_le h0 with h | h
  · rw [← h]; norm_num
  · rw [inv_eq_one_div, le_div_iff₀ h]
    nlinarith

/-- For `1 ≤ t`: `min t t⁻¹ = t⁻¹`. -/
lemma loMinInvOfOneLe {t : ℝ} (h : 1 ≤ t) : min t t⁻¹ = t⁻¹ := by
  refine min_eq_right ?_
  have ht : 0 < t := lt_of_lt_of_le one_pos h
  rw [inv_eq_one_div, div_le_iff₀ ht]
  nlinarith

/-- **The lacunary summation.**  For a `2`-lacunary `σ` with `1 ≤ σ n` and any `s ≥ 0`,
`∑_{n ∈ U} min (σ n · s) (σ n · s)⁻¹ ≤ 4`. -/
theorem loLacSum {σ : ℕ → ℕ} (hσ1 : ∀ n, 1 ≤ σ n) (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1))
    (s : ℝ) (hs : 0 ≤ s) (U : Finset ℕ) :
    ∑ n ∈ U, min ((σ n : ℝ) * s) (((σ n : ℝ) * s)⁻¹) ≤ 4 := by
  classical
  rcases eq_or_lt_of_le hs with hs0 | hspos
  · rw [← hs0]; simp
  have hmono : StrictMono σ := loStrictMonoSigma hσ1 hσ2
  have hinj : Set.InjOn (fun n => ((σ n : ℕ) : ℝ)) ↑U := by
    intro x _ y _ hxy
    exact hmono.injective (Nat.cast_injective hxy)
  set D : Finset ℝ := U.image (fun n => ((σ n : ℕ) : ℝ)) with hD
  have hreindex : ∑ n ∈ U, min ((σ n : ℝ) * s) (((σ n : ℝ) * s)⁻¹)
      = ∑ N ∈ D, min (N * s) ((N * s)⁻¹) := by
    rw [hD, Finset.sum_image]
    intro x hx y hy hxy
    exact hinj hx hy hxy
  rw [hreindex]
  have hDpos : ∀ N ∈ D, 0 < N := by
    intro N hN
    rw [hD] at hN
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hN
    have h1 : (1 : ℝ) ≤ ((σ n : ℕ) : ℝ) := by exact_mod_cast hσ1 n
    linarith
  have hDlac : ∀ M ∈ D, ∀ N ∈ D, M < N → 2 * M ≤ N := by
    intro M hM N hN hMN
    rw [hD] at hM hN
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hM
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hN
    have hij : i < j := by
      by_contra hcon
      have hle : σ j ≤ σ i := hmono.monotone (not_lt.mp hcon)
      have hcast : ((σ j : ℕ) : ℝ) ≤ ((σ i : ℕ) : ℝ) := by exact_mod_cast hle
      linarith
    have h3 : 2 * σ i ≤ σ j := le_trans (hσ2 i) (hmono.monotone (Nat.succ_le_of_lt hij))
    have h3' : 2 * ((σ i : ℕ) : ℝ) ≤ ((σ j : ℕ) : ℝ) := by exact_mod_cast h3
    linarith
  have hsplit : (∑ N ∈ D.filter (fun N => N * s ≤ 1), min (N * s) ((N * s)⁻¹))
      + (∑ N ∈ D.filter (fun N => ¬ (N * s ≤ 1)), min (N * s) ((N * s)⁻¹))
      = ∑ N ∈ D, min (N * s) ((N * s)⁻¹) :=
    Finset.sum_filter_add_sum_filter_not D (fun N => N * s ≤ 1) (fun N => min (N * s) ((N * s)⁻¹))
  rw [← hsplit]
  have hhead : ∑ N ∈ D.filter (fun N => N * s ≤ 1), min (N * s) ((N * s)⁻¹) ≤ 2 := by
    have hfilter : D.filter (fun N => N * s ≤ 1) = D.filter (fun N => s * N ^ 1 ≤ 1) :=
      Finset.filter_congr (s := D) fun N _ => by
        simp only [pow_one]
        constructor <;> intro h <;> linarith
    rw [hfilter]
    have hstep : ∑ N ∈ D.filter (fun N => s * N ^ 1 ≤ 1), min (N * s) ((N * s)⁻¹)
        = ∑ N ∈ D.filter (fun N => s * N ^ 1 ≤ 1), s * N ^ 1 := by
      refine Finset.sum_congr rfl fun N hN => ?_
      have hle : N * s ≤ 1 := by
        have := (Finset.mem_filter.mp hN).2
        simp only [pow_one] at this
        linarith
      have hNpos : 0 < N := hDpos N (Finset.mem_filter.mp hN).1
      rw [loMinInvOfLeOne (mul_nonneg hNpos.le hs) hle, pow_one]
      ring
    rw [hstep]
    refine le_trans (Commons.Analysis.Sum.lacunary_finset_sum_le (Λ := 2) (d := 1) (A := s)
      (D := D) (by norm_num) le_rfl hspos hDpos hDlac (Y := 1) one_pos) ?_
    norm_num
  have htail : ∑ N ∈ D.filter (fun N => ¬ (N * s ≤ 1)), min (N * s) ((N * s)⁻¹) ≤ 2 := by
    have hfilter : D.filter (fun N => ¬ (N * s ≤ 1)) = D.filter (fun N => 1 < s * N ^ 1) :=
      Finset.filter_congr (s := D) fun N _ => by
        simp only [pow_one]
        constructor
        · intro h
          linarith [not_le.mp h]
        · intro h hc
          linarith
    rw [hfilter]
    have hstep : ∑ N ∈ D.filter (fun N => 1 < s * N ^ 1), min (N * s) ((N * s)⁻¹)
        = ∑ N ∈ D.filter (fun N => 1 < s * N ^ 1), (s * N ^ 1)⁻¹ := by
      refine Finset.sum_congr rfl fun N hN => ?_
      have hlt : 1 < N * s := by
        have := (Finset.mem_filter.mp hN).2
        simp only [pow_one] at this
        linarith
      have h1 := loMinInvOfOneLe hlt.le
      have h2 : (N * s)⁻¹ = (s * N ^ 1)⁻¹ := by rw [pow_one]; ring
      rw [h1, h2]
    rw [hstep]
    refine le_trans (Commons.Analysis.Sum.lacunary_finset_sum_inv_le (Λ := 2) (d := 1) (A := s)
      (D := D) (by norm_num) le_rfl hspos hDpos hDlac (X := 1) one_pos) ?_
    norm_num
  linarith [hhead, htail]

/-- **The uniform symbol bound for the linearised deviation kernel.** -/
theorem LoDevSymBound (K : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℕ → ℕ), (∀ n, 1 ≤ σ n) → (∀ n, 2 * σ n ≤ σ (n + 1)) →
      ∀ (U : Finset ℕ) (ω : ℕ → Bool) (θ : ℝ),
        ‖∑' j : ℤ, Work.KMTAreas.A7.lacDevLin K σ U ω j * Work.KMTAreas.ADev.chr j θ‖ ≤ C := by
  obtain ⟨L₀, hL₀pos, hlip⟩ := loFourierLipschitz K
  obtain ⟨A, hApos, hAb⟩ := Work.KMTAreas.A7Hi.bumpSymQuad K hL₀pos.le hlip
  set B : ℝ := ‖lacConst K‖ with hBdef
  set Kc : ℝ := max (A / 4 + 8 * B) (64 * A + 10 * B) with hKcdef
  have hAnn : (0 : ℝ) ≤ A := hApos.le
  have hBnn : (0 : ℝ) ≤ B := by rw [hBdef]; positivity
  have hK1 : A / 4 + 8 * B ≤ Kc := by rw [hKcdef]; exact le_max_left _ _
  have hK2 : 64 * A + 10 * B ≤ Kc := by rw [hKcdef]; exact le_max_right _ _
  have hKnn : (0 : ℝ) ≤ Kc := le_trans (by positivity) hK1
  refine ⟨2 * A + 4 * Kc + 1, by linarith, ?_⟩
  intro σ hσ1 hσ2 U ω θ
  obtain ⟨hnd, h4z, h2πz⟩ := loNearFacts θ
  set s : ℝ := zGap θ with hsdef
  have hs0 : 0 ≤ s := by rw [hsdef]; exact norm_nonneg _
  have hnd0 : 0 ≤ nearDist θ := by rw [nearDist]; positivity
  have h4zs : 4 * nearDist θ ≤ s := by rw [hsdef]; exact h4z
  have h2πzs : s ≤ 2 * Real.pi * nearDist θ := by rw [hsdef]; exact h2πz
  have htri_def : ∀ L : ℕ, ‖(1 : ℂ) - Work.KMTAreas.ADev.triSym L θ‖ ≤ 4 * (2 : ℝ) ^ L * s := by
    intro L; rw [hsdef]; exact Work.KMTAreas.A7Hi.triSym_sub_one_le_zGap h4z L
  have htri_dec : ∀ L : ℕ, s * ‖Work.KMTAreas.ADev.triSym L θ‖ ≤ 5 / (2 : ℝ) ^ L := by
    intro L; rw [hsdef]; exact Work.KMTAreas.A7Hi.zGap_mul_triSym_le L θ
  have hterm : ∀ n ∈ U,
      ‖Work.KMTAreas.ADev.bumpSym K (σ n) θ
          - lacConst K * Work.KMTAreas.ADev.triSym (lacLev σ n) θ‖
        ≤ A * (((σ n : ℕ) : ℝ) ^ 2)⁻¹
          + Kc * min (((σ n : ℕ) : ℝ) * s) ((((σ n : ℕ) : ℝ) * s)⁻¹) := by
    intro n _
    obtain ⟨hb1, hb2⟩ := hAb (σ n) (hσ1 n) θ
    have hσpos : (0 : ℝ) < ((σ n : ℕ) : ℝ) := by
      have hn := hσ1 n
      exact_mod_cast (lt_of_lt_of_le zero_lt_one hn)
    have h2l_ge : ((σ n : ℕ) : ℝ) ≤ 2 * (2 : ℝ) ^ (lacLev σ n) := by
      have h := le_two_pow_lacLev (σ := σ) n
      calc ((σ n : ℕ) : ℝ) ≤ ((2 ^ (lacLev σ n + 1) : ℕ) : ℝ) := by exact_mod_cast h
        _ = 2 * (2 : ℝ) ^ (lacLev σ n) := by push_cast; ring
    by_cases hcase : ((σ n : ℕ) : ℝ) * s ≤ 1
    · -- small scales: the deviation symbol is `O(σ n · s)`
      have hx0 : 0 ≤ ((σ n : ℕ) : ℝ) * s := mul_nonneg hσpos.le hs0
      have hmin : min (((σ n : ℕ) : ℝ) * s) ((((σ n : ℕ) : ℝ) * s)⁻¹)
          = ((σ n : ℕ) : ℝ) * s := by
        refine min_eq_left ?_
        rcases eq_or_lt_of_le hx0 with h0 | hpos
        · rw [← h0]; simp
        · rw [inv_eq_one_div, le_div_iff₀ hpos]
          nlinarith [hcase, hpos]
      have htri1 := htri_def (lacLev σ n)
      have h2l_le : (2 : ℝ) ^ (lacLev σ n) ≤ 2 * ((σ n : ℕ) : ℝ) := by
        have h := pow_lacLev_le (σ := σ) hσ1 n
        calc (2 : ℝ) ^ (lacLev σ n) = (((2 : ℕ) ^ lacLev σ n : ℕ) : ℝ) := by push_cast; ring
          _ ≤ ((2 * σ n : ℕ) : ℝ) := by exact_mod_cast h
          _ = 2 * ((σ n : ℕ) : ℝ) := by push_cast; ring
      have htB : ‖lacConst K * ((1 : ℂ) - Work.KMTAreas.ADev.triSym (lacLev σ n) θ)‖
          ≤ 8 * B * (((σ n : ℕ) : ℝ) * s) := by
        rw [norm_mul, ← hBdef]
        calc B * ‖(1 : ℂ) - Work.KMTAreas.ADev.triSym (lacLev σ n) θ‖
            ≤ B * (4 * (2 : ℝ) ^ (lacLev σ n) * s) := mul_le_mul_of_nonneg_left htri1 hBnn
          _ ≤ B * (4 * (2 * ((σ n : ℕ) : ℝ)) * s) := by
              refine mul_le_mul_of_nonneg_left ?_ hBnn
              nlinarith [h2l_le, hs0]
          _ = 8 * B * (((σ n : ℕ) : ℝ) * s) := by ring
      have hsplit : Work.KMTAreas.ADev.bumpSym K (σ n) θ
            - lacConst K * Work.KMTAreas.ADev.triSym (lacLev σ n) θ
          = (Work.KMTAreas.ADev.bumpSym K (σ n) θ - lacConst K)
            + lacConst K * ((1 : ℂ) - Work.KMTAreas.ADev.triSym (lacLev σ n) θ) := by ring
      rw [hsplit, hmin]
      have hkey : A * (((σ n : ℕ) : ℝ) * nearDist θ) + 8 * B * (((σ n : ℕ) : ℝ) * s)
          ≤ Kc * (((σ n : ℕ) : ℝ) * s) := by
        have hδ : ((σ n : ℕ) : ℝ) * nearDist θ ≤ (((σ n : ℕ) : ℝ) * s) / 4 := by
          nlinarith [h4zs, hσpos.le]
        have h1 : A * (((σ n : ℕ) : ℝ) * nearDist θ)
            ≤ (A / 4) * (((σ n : ℕ) : ℝ) * s) := by nlinarith [hδ, hAnn]
        have h2 : (A / 4 + 8 * B) * (((σ n : ℕ) : ℝ) * s)
            ≤ Kc * (((σ n : ℕ) : ℝ) * s) :=
          mul_le_mul_of_nonneg_right hK1 (mul_nonneg hσpos.le hs0)
        nlinarith [h1, h2]
      calc ‖(Work.KMTAreas.ADev.bumpSym K (σ n) θ - lacConst K)
              + lacConst K * ((1 : ℂ) - Work.KMTAreas.ADev.triSym (lacLev σ n) θ)‖
          ≤ ‖Work.KMTAreas.ADev.bumpSym K (σ n) θ - lacConst K‖
            + ‖lacConst K * ((1 : ℂ) - Work.KMTAreas.ADev.triSym (lacLev σ n) θ)‖ :=
            norm_add_le _ _
        _ ≤ (A * (((σ n : ℕ) : ℝ) ^ 2)⁻¹ + A * (((σ n : ℕ) : ℝ) * nearDist θ))
              + 8 * B * (((σ n : ℕ) : ℝ) * s) := add_le_add hb1 htB
        _ ≤ A * (((σ n : ℕ) : ℝ) ^ 2)⁻¹ + Kc * (((σ n : ℕ) : ℝ) * s) := by linarith [hkey]
    · -- large scales: the deviation symbol is `O((σ n · s)^{-1})`
      have hge : 1 ≤ ((σ n : ℕ) : ℝ) * s := le_of_lt (not_le.mp hcase)
      have hxpos : 0 < ((σ n : ℕ) : ℝ) * s := lt_of_lt_of_le one_pos hge
      have hspos : 0 < s := by
        rcases mul_pos_iff.mp hxpos with h | h
        · exact h.2
        · exact absurd h.2 (not_lt.mpr hs0)
      have hmin : min (((σ n : ℕ) : ℝ) * s) ((((σ n : ℕ) : ℝ) * s)⁻¹)
          = ((((σ n : ℕ) : ℝ) * s)⁻¹) := by
        refine min_eq_right ?_
        rw [inv_eq_one_div, div_le_iff₀ hxpos]
        nlinarith [hge]
      have hxinv : (0 : ℝ) ≤ (((σ n : ℕ) : ℝ) * s)⁻¹ := inv_nonneg.mpr hxpos.le
      have hxinv_le : ((((σ n : ℕ) : ℝ) * s) ^ 2)⁻¹ ≤ ((((σ n : ℕ) : ℝ) * s)⁻¹) := by
        have hsq : ((((σ n : ℕ) : ℝ) * s)⁻¹) ^ 2 ≤ (((σ n : ℕ) : ℝ) * s)⁻¹ := by
          have h1 : (((σ n : ℕ) : ℝ) * s)⁻¹ ≤ 1 := by
            rw [inv_le_one₀ hxpos]; exact hge
          nlinarith [hxinv, h1]
        rwa [inv_pow] at hsq
      have htri_bound : ‖Work.KMTAreas.ADev.triSym (lacLev σ n) θ‖
          ≤ 10 * ((((σ n : ℕ) : ℝ) * s)⁻¹) := by
        have hzy := htri_dec (lacLev σ n)
        have hT : (0 : ℝ) < (2 : ℝ) ^ (lacLev σ n) := by positivity
        have h1 : ‖Work.KMTAreas.ADev.triSym (lacLev σ n) θ‖
            ≤ (5 / (2 : ℝ) ^ (lacLev σ n)) / s := by
          rw [le_div_iff₀ hspos, mul_comm]
          exact hzy
        refine h1.trans ?_
        have hdiv : (5 / (2 : ℝ) ^ (lacLev σ n)) / s
            = 5 / ((2 : ℝ) ^ (lacLev σ n) * s) := by rw [div_div]
        rw [hdiv, inv_eq_one_div, mul_one_div,
          div_le_div_iff₀ (mul_pos hT hspos) hxpos]
        nlinarith [h2l_ge, hs0]
      have htB : ‖lacConst K * Work.KMTAreas.ADev.triSym (lacLev σ n) θ‖
          ≤ 10 * B * ((((σ n : ℕ) : ℝ) * s)⁻¹) := by
        rw [norm_mul, ← hBdef]
        calc B * ‖Work.KMTAreas.ADev.triSym (lacLev σ n) θ‖
            ≤ B * (10 * ((((σ n : ℕ) : ℝ) * s)⁻¹)) :=
              mul_le_mul_of_nonneg_left htri_bound hBnn
          _ = 10 * B * ((((σ n : ℕ) : ℝ) * s)⁻¹) := by ring
      have hb2' : ‖Work.KMTAreas.ADev.bumpSym K (σ n) θ‖
          ≤ A * (((σ n : ℕ) : ℝ) ^ 2)⁻¹ + 64 * A * ((((σ n : ℕ) : ℝ) * s)⁻¹) := by
        refine hb2.trans ?_
        have hδ : (((σ n : ℕ) : ℝ) * s) / (2 * Real.pi)
            ≤ 1 + ((σ n : ℕ) : ℝ) * nearDist θ := by
          have h1 : s / (2 * Real.pi) ≤ nearDist θ := by
            rw [div_le_iff₀ (by positivity)]
            linarith [h2πzs]
          have h2 : ((σ n : ℕ) : ℝ) * (s / (2 * Real.pi))
              ≤ ((σ n : ℕ) : ℝ) * nearDist θ :=
            mul_le_mul_of_nonneg_left h1 hσpos.le
          have h3 : (((σ n : ℕ) : ℝ) * s) / (2 * Real.pi)
              = ((σ n : ℕ) : ℝ) * (s / (2 * Real.pi)) := by ring
          linarith [h2, h3.le, h3.ge]
        have hpos : 0 < (((σ n : ℕ) : ℝ) * s) / (2 * Real.pi) :=
          div_pos hxpos (by positivity)
        have h1δ : (0 : ℝ) < 1 + ((σ n : ℕ) : ℝ) * nearDist θ := by
          nlinarith [hσpos, hnd0]
        have hstep : ((((σ n : ℕ) : ℝ) * s) / (2 * Real.pi)) ^ 2
            ≤ (1 + ((σ n : ℕ) : ℝ) * nearDist θ) ^ 2 := pow_le_pow_left₀ hpos.le hδ 2
        have hinv : ((1 + ((σ n : ℕ) : ℝ) * nearDist θ) ^ 2)⁻¹
            ≤ (((((σ n : ℕ) : ℝ) * s) / (2 * Real.pi)) ^ 2)⁻¹ :=
          (inv_le_inv₀ (pow_pos h1δ 2) (pow_pos hpos 2)).mpr hstep
        have halg : (((((σ n : ℕ) : ℝ) * s) / (2 * Real.pi)) ^ 2)⁻¹
            = 4 * Real.pi ^ 2 * ((((σ n : ℕ) : ℝ) * s) ^ 2)⁻¹ := by
          rw [div_pow, inv_div, div_eq_mul_inv]; ring
        rw [halg] at hinv
        have hpi2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
        have hcmp : 4 * Real.pi ^ 2 * ((((σ n : ℕ) : ℝ) * s) ^ 2)⁻¹
            ≤ 64 * ((((σ n : ℕ) : ℝ) * s)⁻¹) := by
          have h4 : 4 * Real.pi ^ 2 ≤ 64 := by nlinarith [hpi2]
          calc 4 * Real.pi ^ 2 * ((((σ n : ℕ) : ℝ) * s) ^ 2)⁻¹
              ≤ 64 * ((((σ n : ℕ) : ℝ) * s) ^ 2)⁻¹ :=
                mul_le_mul_of_nonneg_right h4 (inv_nonneg.mpr (sq_nonneg _))
            _ ≤ 64 * ((((σ n : ℕ) : ℝ) * s)⁻¹) :=
                mul_le_mul_of_nonneg_left hxinv_le (by norm_num)
        calc A * (((σ n : ℕ) : ℝ) ^ 2)⁻¹
                + A * ((1 + ((σ n : ℕ) : ℝ) * nearDist θ) ^ 2)⁻¹
            ≤ A * (((σ n : ℕ) : ℝ) ^ 2)⁻¹
                + A * (4 * Real.pi ^ 2 * ((((σ n : ℕ) : ℝ) * s) ^ 2)⁻¹) :=
              add_le_add le_rfl (mul_le_mul_of_nonneg_left hinv hAnn)
          _ ≤ A * (((σ n : ℕ) : ℝ) ^ 2)⁻¹
                + A * (64 * ((((σ n : ℕ) : ℝ) * s)⁻¹)) :=
              add_le_add le_rfl (mul_le_mul_of_nonneg_left hcmp hAnn)
          _ = A * (((σ n : ℕ) : ℝ) ^ 2)⁻¹ + 64 * A * ((((σ n : ℕ) : ℝ) * s)⁻¹) := by ring
      rw [hmin]
      calc ‖Work.KMTAreas.ADev.bumpSym K (σ n) θ
              - lacConst K * Work.KMTAreas.ADev.triSym (lacLev σ n) θ‖
          ≤ ‖Work.KMTAreas.ADev.bumpSym K (σ n) θ‖
            + ‖lacConst K * Work.KMTAreas.ADev.triSym (lacLev σ n) θ‖ := norm_sub_le _ _
        _ ≤ (A * (((σ n : ℕ) : ℝ) ^ 2)⁻¹ + 64 * A * ((((σ n : ℕ) : ℝ) * s)⁻¹))
              + 10 * B * ((((σ n : ℕ) : ℝ) * s)⁻¹) := add_le_add hb2' htB
        _ = A * (((σ n : ℕ) : ℝ) ^ 2)⁻¹
              + (64 * A + 10 * B) * ((((σ n : ℕ) : ℝ) * s)⁻¹) := by ring
        _ ≤ A * (((σ n : ℕ) : ℝ) ^ 2)⁻¹
              + Kc * ((((σ n : ℕ) : ℝ) * s)⁻¹) := by
            exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hK2 hxinv)
  have hmain : ‖∑' j : ℤ, Work.KMTAreas.A7.lacDevLin K σ U ω j
        * Work.KMTAreas.ADev.chr j θ‖
      ≤ ∑ n ∈ U, (A * (((σ n : ℕ) : ℝ) ^ 2)⁻¹
          + Kc * min (((σ n : ℕ) : ℝ) * s) ((((σ n : ℕ) : ℝ) * s)⁻¹)) := by
    rw [lacDevLin_tsum_eq K σ hσ1 U ω θ]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    rw [lacDevPerScaleSym K σ hσ1 n θ]
    refine le_trans ?_ (hterm n hn)
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (Work.KMTAreas.ADev.norm_bSign_le ω n)
  calc ‖∑' j : ℤ, Work.KMTAreas.A7.lacDevLin K σ U ω j * Work.KMTAreas.ADev.chr j θ‖
      ≤ ∑ n ∈ U, (A * (((σ n : ℕ) : ℝ) ^ 2)⁻¹
          + Kc * min (((σ n : ℕ) : ℝ) * s) ((((σ n : ℕ) : ℝ) * s)⁻¹)) := hmain
    _ = A * (∑ n ∈ U, (((σ n : ℕ) : ℝ) ^ 2)⁻¹)
          + Kc * (∑ n ∈ U, min (((σ n : ℕ) : ℝ) * s) ((((σ n : ℕ) : ℝ) * s)⁻¹)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ A * 2 + Kc * 4 := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left (loSumInvSqScale σ hσ1 hσ2 U) hAnn
        · exact mul_le_mul_of_nonneg_left (loLacSum hσ1 hσ2 s hs0 U) hKnn
    _ ≤ 2 * A + 4 * Kc + 1 := by linarith

end

end Work.KMTAreas.A7

