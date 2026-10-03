import Mathlib
import Submission.Work.FITop4.Red5.piecesSetup
import Submission.Work.FITop4.Red5.primAnn_rpow_weight
import Submission.Work.FITop4.Red5.window_T2_shell_reduce
import Submission.Work.FITop4.Red5.window_T2_sph_conv
import Submission.Work.FITop4.Red5.isPrimitive_of_sqfree_primary
import Submission.Work.FITop4.Red5.window_T2_shell_arith

set_option autoImplicit false
set_option maxHeartbeats 3200000

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The window shell count for a single `z`, dominating the reduced `T2` summand. -/
def wscCount (x Mn : ℕ) (θ : ℝ) (z : GaussianInt) : ℝ :=
  ∑ m ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter
        (fun m : ℕ => (x : ℝ) < (m : ℝ) * (Work.FIPlan.gnorm z : ℝ)
          ∧ (m : ℝ) * (Work.FIPlan.gnorm z : ℝ) ≤ (x : ℝ) * (1 + θ)),
    ∑ w ∈ wSph m, (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)

lemma wscCount_nonneg (x Mn : ℕ) (θ : ℝ) (z : GaussianInt) : 0 ≤ wscCount x Mn θ z := by
  rw [wscCount]
  exact Finset.sum_nonneg (fun m _ => Finset.sum_nonneg (fun w _ => Zint_nonneg _))


/-- The per-`z` crux: the `θ`-window shell sum is dominated by the crux's interval count.
The crux is applied to the interval `(min W - 1, max W]`, whose width is `< 2θMn + 1`. -/
theorem window_T2_perz_of_crux_local
    (Cc : ℝ) (hcC : 0 < Cc)
    (hcrux : ∀ (z : GaussianInt) (X₁ X₂ Mn : ℕ) (θ : ℝ),
      Work.FIPlan.IsPrimitive z → 1 ≤ Work.FIPlan.gnorm z → 1 ≤ Mn →
      Mn ≤ X₁ → X₁ ≤ X₂ → X₂ ≤ 2 * Mn → (X₂ - X₁ : ℝ) ≤ 2 * θ * Mn →
      (∑ w ∈ (Work.FIPlan.gBox (2 * (Mn : ℤ))).filter
          (fun w => X₁ < Work.FIPlan.gnorm w ∧ Work.FIPlan.gnorm w ≤ X₂),
          (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
        ≤ Cc * ((X₂ - X₁ : ℝ) * ((X₁ : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ (-(1 : ℝ) / 4)
            + ((X₂ : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1 : ℝ) / 4)))
    (x Mn : ℕ) (θ : ℝ) (hMn : 1 ≤ Mn) (hθ : 0 < θ)
    (z : GaussianInt) (hprim : Work.FIPlan.IsPrimitive z) (hz1 : 1 ≤ Work.FIPlan.gnorm z) :
    wscCount x Mn θ z
      ≤ Cc * ((2 * θ * (Mn : ℝ) + 1) * ((Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ (-(1 : ℝ) / 4)
          + ((2 * (Mn : ℝ)) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1 : ℝ) / 4)) := by
  rw [wscCount]
  set W : Finset ℕ := (Finset.Icc (Mn + 1) (2 * Mn)).filter
      (fun m : ℕ => (x : ℝ) < (m : ℝ) * (Work.FIPlan.gnorm z : ℝ)
        ∧ (m : ℝ) * (Work.FIPlan.gnorm z : ℝ) ≤ (x : ℝ) * (1 + θ)) with hWdef
  have hu : (0 : ℝ) < (Work.FIPlan.gnorm z : ℝ) := by
    exact_mod_cast (by omega : 0 < Work.FIPlan.gnorm z)
  have hMnR : (0 : ℝ) < (Mn : ℝ) := by exact_mod_cast (by omega : 0 < Mn)
  have hMnR1 : (1 : ℝ) ≤ (Mn : ℝ) := by exact_mod_cast hMn
  have hmem : ∀ m ∈ W, Mn + 1 ≤ m ∧ m ≤ 2 * Mn
      ∧ (x : ℝ) < (m : ℝ) * (Work.FIPlan.gnorm z : ℝ)
      ∧ (m : ℝ) * (Work.FIPlan.gnorm z : ℝ) ≤ (x : ℝ) * (1 + θ) := by
    intro m hm
    rw [hWdef, Finset.mem_filter, Finset.mem_Icc] at hm
    exact ⟨hm.1.1, hm.1.2, hm.2.1, hm.2.2⟩
  by_cases hne : W.Nonempty
  · set A : ℕ := W.min' hne with hAdef
    set B : ℕ := W.max' hne with hBdef
    have hAW : A ∈ W := by rw [hAdef]; exact Finset.min'_mem W hne
    have hBW : B ∈ W := by rw [hBdef]; exact Finset.max'_mem W hne
    obtain ⟨hA1, hA2, hA3, hA4⟩ := hmem A hAW
    obtain ⟨hB1, hB2, hB3, hB4⟩ := hmem B hBW
    have hA1' : 1 ≤ A := by omega
    have hAleB : A ≤ B := by rw [hAdef, hBdef]; exact Finset.min'_le W B hBW
    have hA1c : ((A - 1 : ℕ) : ℝ) = (A : ℝ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ A by omega)]; norm_num
    have hWeq : ((B - (A - 1) : ℕ) : ℝ) = (B : ℝ) - ((A - 1 : ℕ) : ℝ) :=
      Nat.cast_sub (by omega : A - 1 ≤ B)
    have hstep1 : (∑ m ∈ W, ∑ w ∈ wSph m, (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
        ≤ ∑ m ∈ Finset.Icc A B, ∑ w ∈ wSph m, (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        rw [Finset.mem_Icc]
        exact ⟨by rw [hAdef]; exact Finset.min'_le W m hm,
               by rw [hBdef]; exact Finset.le_max' W m hm⟩
      · intro m _ _; exact Finset.sum_nonneg (fun w _ => Zint_nonneg _)
    have hstep2 := sum_Icc_wSph_le_box z (Mn := Mn) (A := A) (B := B) hMn hA1' hB2
    have hfilter : ((Work.FIPlan.gBox (2 * (Mn : ℤ))).filter
          (fun w => A ≤ Work.FIPlan.gnorm w ∧ Work.FIPlan.gnorm w ≤ B))
        = ((Work.FIPlan.gBox (2 * (Mn : ℤ))).filter
          (fun w => A - 1 < Work.FIPlan.gnorm w ∧ Work.FIPlan.gnorm w ≤ B)) := by
      apply Finset.filter_congr
      intro w _
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    rw [hfilter] at hstep2
    have hcruxapp := hcrux z (A - 1) B Mn (((B - (A - 1) : ℕ) : ℝ))
      hprim hz1 hMn (by omega) (by omega) (by omega)
      (by
        have hWnn : (0 : ℝ) ≤ ((B - (A - 1) : ℕ) : ℝ) := Nat.cast_nonneg _
        rw [← hWeq]; nlinarith [hWnn, hMnR1])
    rw [← hWeq] at hcruxapp
    have hWb : ((B - (A - 1) : ℕ) : ℝ) ≤ 2 * θ * (Mn : ℝ) + 1 := by
      have h1 : ((B : ℝ) - (A : ℝ)) * (Work.FIPlan.gnorm z : ℝ) < θ * (x : ℝ) := by
        nlinarith [hA3, hB4]
      have h2 : ((B : ℝ) - (A : ℝ)) * (Work.FIPlan.gnorm z : ℝ)
          < θ * (A : ℝ) * (Work.FIPlan.gnorm z : ℝ) := by
        nlinarith [h1, hA3, hθ]
      have h3 : (B : ℝ) - (A : ℝ) < θ * (A : ℝ) := lt_of_mul_lt_mul_right h2 hu.le
      have hA2R : (A : ℝ) ≤ 2 * (Mn : ℝ) := by exact_mod_cast hA2
      have h4 : (B : ℝ) - (A : ℝ) < 2 * θ * (Mn : ℝ) := by nlinarith [h3, hA2R, hθ]
      have hcast : ((B - (A - 1) : ℕ) : ℝ) = (B : ℝ) - (A : ℝ) + 1 := by
        rw [hWeq, hA1c]; ring
      rw [hcast]; linarith
    have ht1 : (((B - (A - 1) : ℕ) : ℝ))
          * ((((A - 1 : ℕ)) : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ (-(1 : ℝ) / 4)
        ≤ (2 * θ * (Mn : ℝ) + 1) * ((Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ (-(1 : ℝ) / 4) := by
      have hA1R : (Mn : ℝ) ≤ ((A - 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : Mn ≤ A - 1)
      have hle1 : (Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ)
          ≤ ((A - 1 : ℕ) : ℝ) * (Work.FIPlan.gnorm z : ℝ) :=
        mul_le_mul_of_nonneg_right hA1R hu.le
      have hp1 : (((A - 1 : ℕ) : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ (-(1 : ℝ) / 4)
          ≤ ((Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ (-(1 : ℝ) / 4) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hle1 (by norm_num)
      have hcnn : (0 : ℝ) ≤ (((A - 1 : ℕ) : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ (-(1 : ℝ) / 4) :=
        Real.rpow_nonneg (by positivity) _
      have hb1 : (0 : ℝ) ≤ 2 * θ * (Mn : ℝ) + 1 := by positivity
      exact mul_le_mul hWb hp1 hcnn hb1
    have ht2 : ((B : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1 : ℝ) / 4)
        ≤ ((2 * (Mn : ℝ)) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1 : ℝ) / 4) := by
      have hB2R : (B : ℝ) ≤ 2 * (Mn : ℝ) := by exact_mod_cast hB2
      exact Real.rpow_le_rpow (by positivity)
        (mul_le_mul_of_nonneg_right hB2R hu.le) (by norm_num)
    have hcomb := add_le_add ht1 ht2
    calc (∑ m ∈ W, ∑ w ∈ wSph m, (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
        ≤ ∑ m ∈ Finset.Icc A B, ∑ w ∈ wSph m, (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) := hstep1
      _ ≤ ∑ w ∈ (Work.FIPlan.gBox (2 * (Mn : ℤ))).filter
              (fun w => A - 1 < Work.FIPlan.gnorm w ∧ Work.FIPlan.gnorm w ≤ B),
            (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) := hstep2
      _ ≤ Cc * ((((B - (A - 1) : ℕ) : ℝ))
              * ((((A - 1 : ℕ)) : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ (-(1 : ℝ) / 4)
            + ((B : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1 : ℝ) / 4)) := hcruxapp
      _ ≤ Cc * ((2 * θ * (Mn : ℝ) + 1) * ((Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ (-(1 : ℝ) / 4)
            + ((2 * (Mn : ℝ)) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1 : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left hcomb hcC.le
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty]
    have hb1 : (0 : ℝ) < 2 * θ * (Mn : ℝ) + 1 := by nlinarith [hθ, hMnR]
    have hb2 : (0 : ℝ) < ((Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ (-(1 : ℝ) / 4) :=
      Real.rpow_pos_of_pos (by positivity) _
    have hb3 : (0 : ℝ) ≤ ((2 * (Mn : ℝ)) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1 : ℝ) / 4) :=
      Real.rpow_nonneg (by positivity) _
    have hpos : (0 : ℝ) < (2 * θ * (Mn : ℝ) + 1) * ((Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ (-(1 : ℝ) / 4)
        + ((2 * (Mn : ℝ)) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1 : ℝ) / 4) := by
      nlinarith [mul_pos hb1 hb2, hb3]
    exact mul_nonneg hcC.le hpos.le

/-- Assembly core: from the per-`z` crux, the weight-sum input and the closing real inequality,
the `T2` window bound follows. -/
theorem window_T2_shell_of_crux_core
    (Cc : ℝ) (hcC : 0 < Cc)
    (hcrux : ∀ (z : GaussianInt) (X₁ X₂ Mn : ℕ) (θ : ℝ),
      Work.FIPlan.IsPrimitive z → 1 ≤ Work.FIPlan.gnorm z → 1 ≤ Mn →
      Mn ≤ X₁ → X₁ ≤ X₂ → X₂ ≤ 2 * Mn → (X₂ - X₁ : ℝ) ≤ 2 * θ * Mn →
      (∑ w ∈ (Work.FIPlan.gBox (2 * (Mn : ℤ))).filter
          (fun w => X₁ < Work.FIPlan.gnorm w ∧ Work.FIPlan.gnorm w ≤ X₂),
          (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
        ≤ Cc * ((X₂ - X₁ : ℝ) * ((X₁ : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ (-(1 : ℝ) / 4)
            + ((X₂ : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1 : ℝ) / 4)))
    (C2 : ℝ) (hC2 : 0 < C2)
    (hW : ∀ (N : ℕ) (σ : ℝ), 1 ≤ N → -(1 : ℝ) / 2 ≤ σ → σ ≤ 1 / 4 →
      (∑ z ∈ primAnn (2 * N),
          |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
            * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
            * (Work.FIPlan.gnorm z : ℝ) ^ σ)
        ≤ C2 * (N : ℝ) ^ (1 + σ) * (Real.log (2 * (N : ℝ) + 2)) ^ (100 : ℕ))
    (hperz : ∀ (x Mn : ℕ) (θ : ℝ), 1 ≤ Mn → 0 < θ → ∀ (z : GaussianInt),
      Work.FIPlan.IsPrimitive z → 1 ≤ Work.FIPlan.gnorm z →
      wscCount x Mn θ z
        ≤ Cc * ((2 * θ * (Mn : ℝ) + 1) * ((Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ (-(1 : ℝ) / 4)
            + ((2 * (Mn : ℝ)) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1 : ℝ) / 4)))
    (harith : ∀ (Mn N : ℕ) (θ : ℝ), 1 ≤ Mn → 1 ≤ N → 0 < θ → θ ≤ 1 / 4 →
      1 ≤ θ * (N : ℝ) ^ ((1 : ℝ) / 2) → 2 * (N : ℝ) ≤ θ ^ (2 : ℕ) * (Mn : ℝ) →
      (2 * θ * (Mn : ℝ) + 1) * (Mn : ℝ) ^ (-(1 : ℝ) / 4) * (N : ℝ) ^ ((3 : ℝ) / 4)
        + (2 * (Mn : ℝ)) ^ ((1 : ℝ) / 4) * (N : ℝ) ^ ((5 : ℝ) / 4)
        ≤ 10 * θ * ((Mn : ℝ) * (N : ℝ)) ^ ((3 : ℝ) / 4)) :
    ∃ c : ℝ, 0 < c ∧ ∀ (x N Mn : ℕ) (τ θ : ℝ) (K K' : ℕ)
      (a : Fin K → ℝ) (p : Fin K → ℝ → ℝ) (φ : Fin K' → ℝ) (q : Fin K' → ℝ → ℝ)
      (Pa : Fin K → Fin K' → Work.FITop.Params),
      (4 ≤ x) → (1 ≤ Mn) → (1 ≤ N) → (0 < θ) → (θ ≤ 1 / 4) →
      ((N : ℝ) ^ (2 : ℕ) ≤ (x : ℝ)) →
      (1 ≤ θ * (N : ℝ) ^ ((1 : ℝ) / 2)) →
      2 * (N : ℝ) ≤ θ ^ (2 : ℕ) * (Mn : ℝ) →
      (∀ i k, (Pa i k).M = (Mn : ℝ)) → (∀ i k, (Pa i k).N = a i) →
      (∀ i k, (Pa i k).τ = τ) →
      (∀ i, (N : ℝ) ≤ a i) → (∀ i, a i ≤ 2 * (N : ℝ)) →
      (∀ i u, 0 ≤ p i u) → (∀ i u, p i u ≤ 1) →
      (∀ i u, p i u ≠ 0 → a i < u ∧ u ≤ (1 + θ) * a i) →
      (∀ u, (N : ℝ) < u → u ≤ 2 * (N : ℝ) → (∑ i, p i u) ≤ 1) →
      (∀ k α, 0 ≤ q k α) → (∀ k α, q k α ≤ 1) → (∀ k, q k 0 = 0) →
      (∀ k α, q k α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ) →
      (∀ α, -Real.pi ≤ α → α ≤ Real.pi → (∑ k, q k (α - φ k)) = 1) →
      (∀ (i : Fin K) (k : Fin K') (z : GaussianInt),
        Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z ≠ 0 →
          Work.FIPlan.IsPrimitive z) →
      ((N : ℝ) ≤ (Mn : ℝ)) →
      (∑ i, ∑ k, ∑ mm ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter
          (fun m : ℕ => (m : ℝ) * a i < (x : ℝ)),
          ∑ w ∈ Work.FITop4.Red5.wSph mm, ∑ z ∈ Work.FITop4.Red5.primAnn (2 * N),
            2 * (if (mm : ℝ) * (Work.FIPlan.gnorm z : ℝ) > (x : ℝ) then (1 : ℝ) else 0)
              * ‖Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z
                  * Work.FITop3.Zc w z‖)
        ≤ c * θ * ((Mn : ℝ) * (N : ℝ)) ^ ((3 : ℝ) / 4) * (Real.log (x : ℝ)) ^ (100 : ℕ) := by
  refine ⟨20 * Cc * C2, by positivity, ?_⟩
  intro x N Mn τ θ K K' a p φ q Pa hx4 hMn1 hN1 hθ0 hθ14 hN2x hθsq h2N hPaM hPaN hPaτ
    haN ha2 hp0 hp1 hpsup hpsumle hq0 hq1 hq0z hqsup hang hprim hMnN
  have hred := window_T2_shell_reduce x N Mn τ θ K K' a p φ q Pa hN1 hθ0 haN hp0 hpsup hpsumle hq0 hang
  set u : GaussianInt → ℝ := fun z => (Work.FIPlan.gnorm z : ℝ) with hudef
  set wt : GaussianInt → ℝ := fun z =>
    |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
      * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) with hwtdef
  set F : Finset GaussianInt :=
    (primAnn (2 * N)).filter (fun z => (N : ℝ) < (Work.FIPlan.gnorm z : ℝ)) with hFdef
  set L : ℝ := (Real.log (2 * (N : ℝ) + 2)) ^ (100 : ℕ) with hLdef
  set S1 : ℝ := ∑ z ∈ F, wt z * (Work.FIPlan.gnorm z : ℝ) ^ (-(1 : ℝ) / 4) with hS1def
  set S2 : ℝ := ∑ z ∈ F, wt z * (Work.FIPlan.gnorm z : ℝ) ^ ((1 : ℝ) / 4) with hS2def
  have hwt0 : ∀ z, 0 ≤ wt z := by intro z; rw [hwtdef]; positivity
  have hL0 : 0 ≤ L := by rw [hLdef]; positivity
  -- (1) per-`z` dominance of the reduced sum
  have hsum1 : (∑ z ∈ F, wt z * wscCount x Mn θ z)
      ≤ ∑ z ∈ F, wt z * (Cc * ((2 * θ * (Mn : ℝ) + 1) * ((Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ (-(1 : ℝ) / 4)
            + ((2 * (Mn : ℝ)) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1 : ℝ) / 4))) := by
    apply Finset.sum_le_sum
    intro z hz
    rw [hFdef, Finset.mem_filter] at hz
    obtain ⟨hzann, hzN⟩ := hz
    by_cases hmu : (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ) = 0
    · have hwtz : wt z = 0 := by rw [hwtdef]; simp [hmu]
      rw [hwtz]; simp
    · have hmunz : ArithmeticFunction.moebius (Work.FIPlan.gnorm z) ≠ 0 := by
        intro h; exact hmu (by rw [h]; norm_num)
      have hprimz : Work.FIPlan.IsPrimitive z := by
        apply isPrimitive_of_sqfree_primary
        · rwa [ArithmeticFunction.moebius_ne_zero_iff_squarefree] at hmunz
        · exact (wsr_mem_primAnn_iff.mp hzann).2.2.2
      have hz1 : 1 ≤ Work.FIPlan.gnorm z := (wsr_mem_primAnn_iff.mp hzann).2.1
      have hSC := hperz x Mn θ hMn1 hθ0 z hprimz hz1
      exact mul_le_mul_of_nonneg_left hSC (hwt0 z)
  -- (2) algebraic rewriting of the second sum
  have hsum2 : (∑ z ∈ F, wt z * (Cc * ((2 * θ * (Mn : ℝ) + 1) * ((Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ (-(1 : ℝ) / 4)
            + ((2 * (Mn : ℝ)) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1 : ℝ) / 4))))
      = Cc * ((2 * θ * (Mn : ℝ) + 1) * (Mn : ℝ) ^ (-(1 : ℝ) / 4) * S1
              + (2 * (Mn : ℝ)) ^ ((1 : ℝ) / 4) * S2) := by
    have hpt : ∀ z : GaussianInt,
        wt z * (Cc * ((2 * θ * (Mn : ℝ) + 1) * ((Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ (-(1 : ℝ) / 4)
            + ((2 * (Mn : ℝ)) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1 : ℝ) / 4)))
          = Cc * ((2 * θ * (Mn : ℝ) + 1) * (Mn : ℝ) ^ (-(1 : ℝ) / 4) * (wt z * (Work.FIPlan.gnorm z : ℝ) ^ (-(1 : ℝ) / 4))
              + (2 * (Mn : ℝ)) ^ ((1 : ℝ) / 4) * (wt z * (Work.FIPlan.gnorm z : ℝ) ^ ((1 : ℝ) / 4))) := by
      intro z
      rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ (Mn : ℝ)) (by positivity : (0 : ℝ) ≤ (Work.FIPlan.gnorm z : ℝ)),
          Real.mul_rpow (by positivity : (0 : ℝ) ≤ (2 * (Mn : ℝ))) (by positivity : (0 : ℝ) ≤ (Work.FIPlan.gnorm z : ℝ))]
      ring
    rw [Finset.sum_congr rfl (fun z _ => hpt z)]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← hS1def, ← hS2def]
  -- (3) the weight sums
  have hS1 : S1 ≤ C2 * (N : ℝ) ^ ((3 : ℝ) / 4) * L := by
    have h := hW N (-(1 : ℝ) / 4) hN1 (by norm_num) (by norm_num)
    have hexp : (1 : ℝ) + (-(1 : ℝ) / 4) = (3 : ℝ) / 4 := by norm_num
    rw [hexp, ← hLdef] at h
    have hsub : F ⊆ primAnn (2 * N) := by rw [hFdef]; exact Finset.filter_subset _ _
    rw [hS1def]
    calc (∑ z ∈ F, wt z * (Work.FIPlan.gnorm z : ℝ) ^ (-(1 : ℝ) / 4))
        = ∑ z ∈ F, |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
            * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
            * (Work.FIPlan.gnorm z : ℝ) ^ (-(1 : ℝ) / 4) := by
          apply Finset.sum_congr rfl; intro z _; simp only [hwtdef]
      _ ≤ ∑ z ∈ primAnn (2 * N), |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
            * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
            * (Work.FIPlan.gnorm z : ℝ) ^ (-(1 : ℝ) / 4) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => by positivity)
      _ ≤ C2 * (N : ℝ) ^ ((3 : ℝ) / 4) * L := h
  have hS2 : S2 ≤ C2 * (N : ℝ) ^ ((5 : ℝ) / 4) * L := by
    have h := hW N ((1 : ℝ) / 4) hN1 (by norm_num) (by norm_num)
    have hexp : (1 : ℝ) + (1 : ℝ) / 4 = (5 : ℝ) / 4 := by norm_num
    rw [hexp, ← hLdef] at h
    have hsub : F ⊆ primAnn (2 * N) := by rw [hFdef]; exact Finset.filter_subset _ _
    rw [hS2def]
    calc (∑ z ∈ F, wt z * (Work.FIPlan.gnorm z : ℝ) ^ ((1 : ℝ) / 4))
        = ∑ z ∈ F, |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
            * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
            * (Work.FIPlan.gnorm z : ℝ) ^ ((1 : ℝ) / 4) := by
          apply Finset.sum_congr rfl; intro z _; simp only [hwtdef]
      _ ≤ ∑ z ∈ primAnn (2 * N), |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
            * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
            * (Work.FIPlan.gnorm z : ℝ) ^ ((1 : ℝ) / 4) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => by positivity)
      _ ≤ C2 * (N : ℝ) ^ ((5 : ℝ) / 4) * L := h
  -- (4) closing arithmetic
  have hT : (2 * θ * (Mn : ℝ) + 1) * (Mn : ℝ) ^ (-(1 : ℝ) / 4) * S1
        + (2 * (Mn : ℝ)) ^ ((1 : ℝ) / 4) * S2
      ≤ C2 * L * (10 * θ * ((Mn : ℝ) * (N : ℝ)) ^ ((3 : ℝ) / 4)) := by
    have hA : (2 * θ * (Mn : ℝ) + 1) * (Mn : ℝ) ^ (-(1 : ℝ) / 4) * S1
        ≤ (2 * θ * (Mn : ℝ) + 1) * (Mn : ℝ) ^ (-(1 : ℝ) / 4) * (C2 * (N : ℝ) ^ ((3 : ℝ) / 4) * L) :=
      mul_le_mul_of_nonneg_left hS1 (by positivity)
    have hB : (2 * (Mn : ℝ)) ^ ((1 : ℝ) / 4) * S2
        ≤ (2 * (Mn : ℝ)) ^ ((1 : ℝ) / 4) * (C2 * (N : ℝ) ^ ((5 : ℝ) / 4) * L) :=
      mul_le_mul_of_nonneg_left hS2 (by positivity)
    have har := harith Mn N θ hMn1 hN1 hθ0 hθ14 hθsq h2N
    have hkey : C2 * (N : ℝ) ^ ((3 : ℝ) / 4) * L * ((2 * θ * (Mn : ℝ) + 1) * (Mn : ℝ) ^ (-(1 : ℝ) / 4))
          + C2 * (N : ℝ) ^ ((5 : ℝ) / 4) * L * (2 * (Mn : ℝ)) ^ ((1 : ℝ) / 4)
        ≤ C2 * L * (10 * θ * ((Mn : ℝ) * (N : ℝ)) ^ ((3 : ℝ) / 4)) := by
      have hC2L : (0 : ℝ) ≤ C2 * L := by positivity
      have har2 := mul_le_mul_of_nonneg_left har hC2L
      linarith [hA, hB, har2]
    linarith [hA, hB, hkey]
  -- (5) log comparison
  have hLle : L ≤ (Real.log (x : ℝ)) ^ (100 : ℕ) := by
    have hN16 : 16 ≤ N := by
      have hsqrt4 : (4 : ℝ) ≤ Real.sqrt (N : ℝ) := by
        rw [Real.sqrt_eq_rpow]
        have h1 : (1 : ℝ) / θ ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
          rw [div_le_iff₀ hθ0]; nlinarith [hθsq]
        have h2 : (4 : ℝ) ≤ 1 / θ := by rw [le_div_iff₀ hθ0]; nlinarith [hθ14]
        linarith
      have h16 : (16 : ℝ) ≤ (N : ℝ) := by
        have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ (N : ℝ) by positivity)
        have hsn := Real.sqrt_nonneg (N : ℝ)
        nlinarith [hsqrt4, hsq, hsn]
      exact_mod_cast h16
    rw [hLdef]
    apply pow_le_pow_left₀ (Real.log_nonneg (by linarith [hN1] : (1 : ℝ) ≤ 2 * (N : ℝ) + 2))
    apply Real.log_le_log (by positivity)
    have h2 : 2 * N + 2 ≤ N ^ 2 := by nlinarith [hN16]
    have h3 : 2 * (N : ℝ) + 2 ≤ (N : ℝ) ^ 2 := by
      have : ((2 * N + 2 : ℕ) : ℝ) ≤ ((N ^ 2 : ℕ) : ℝ) := by exact_mod_cast h2
      push_cast at this
      linarith
    linarith [hN2x, h3]
  -- (6) assembly
  have hred' : (∑ i, ∑ k, ∑ mm ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter
          (fun m : ℕ => (m : ℝ) * a i < (x : ℝ)),
          ∑ w ∈ Work.FITop4.Red5.wSph mm, ∑ z ∈ Work.FITop4.Red5.primAnn (2 * N),
            2 * (if (mm : ℝ) * (Work.FIPlan.gnorm z : ℝ) > (x : ℝ) then (1 : ℝ) else 0)
              * ‖Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z
                  * Work.FITop3.Zc w z‖)
      ≤ 2 * (∑ z ∈ F, wt z * wscCount x Mn θ z) := by
    rw [hFdef]
    simp only [hwtdef]
    exact hred
  calc (∑ i, ∑ k, ∑ mm ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter
          (fun m : ℕ => (m : ℝ) * a i < (x : ℝ)),
          ∑ w ∈ Work.FITop4.Red5.wSph mm, ∑ z ∈ Work.FITop4.Red5.primAnn (2 * N),
            2 * (if (mm : ℝ) * (Work.FIPlan.gnorm z : ℝ) > (x : ℝ) then (1 : ℝ) else 0)
              * ‖Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z
                  * Work.FITop3.Zc w z‖)
      ≤ 2 * (∑ z ∈ F, wt z * wscCount x Mn θ z) := hred'
    _ ≤ 2 * (∑ z ∈ F, wt z * (Cc * ((2 * θ * (Mn : ℝ) + 1) * ((Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ (-(1 : ℝ) / 4)
            + ((2 * (Mn : ℝ)) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1 : ℝ) / 4)))) := by linarith [hsum1]
    _ = 2 * (Cc * ((2 * θ * (Mn : ℝ) + 1) * (Mn : ℝ) ^ (-(1 : ℝ) / 4) * S1
              + (2 * (Mn : ℝ)) ^ ((1 : ℝ) / 4) * S2)) := by rw [hsum2]
    _ = 2 * Cc * ((2 * θ * (Mn : ℝ) + 1) * (Mn : ℝ) ^ (-(1 : ℝ) / 4) * S1
              + (2 * (Mn : ℝ)) ^ ((1 : ℝ) / 4) * S2) := by ring
    _ ≤ 2 * Cc * (C2 * L * (10 * θ * ((Mn : ℝ) * (N : ℝ)) ^ ((3 : ℝ) / 4))) := by
        apply mul_le_mul_of_nonneg_left hT (by positivity)
    _ = (20 * Cc * C2) * θ * ((Mn : ℝ) * (N : ℝ)) ^ ((3 : ℝ) / 4) * L := by ring
    _ ≤ (20 * Cc * C2) * θ * ((Mn : ℝ) * (N : ℝ)) ^ ((3 : ℝ) / 4) * (Real.log (x : ℝ)) ^ (100 : ℕ) := by
        apply mul_le_mul_of_nonneg_left hLle
        positivity

theorem window_T2_shell_of_crux
    (Cc : ℝ) (hcC : 0 < Cc)
    (hcrux : ∀ (z : GaussianInt) (X₁ X₂ Mn : ℕ) (θ : ℝ),
      Work.FIPlan.IsPrimitive z → 1 ≤ Work.FIPlan.gnorm z → 1 ≤ Mn →
      Mn ≤ X₁ → X₁ ≤ X₂ → X₂ ≤ 2 * Mn → (X₂ - X₁ : ℝ) ≤ 2 * θ * Mn →
      (∑ w ∈ (Work.FIPlan.gBox (2 * (Mn : ℤ))).filter
          (fun w => X₁ < Work.FIPlan.gnorm w ∧ Work.FIPlan.gnorm w ≤ X₂),
          (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
        ≤ Cc * ((X₂ - X₁ : ℝ) * ((X₁ : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ (-(1 : ℝ) / 4)
            + ((X₂ : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1 : ℝ) / 4))) :
    ∃ c : ℝ, 0 < c ∧ ∀ (x N Mn : ℕ) (τ θ : ℝ) (K K' : ℕ)
      (a : Fin K → ℝ) (p : Fin K → ℝ → ℝ) (φ : Fin K' → ℝ) (q : Fin K' → ℝ → ℝ)
      (Pa : Fin K → Fin K' → Work.FITop.Params),
      (4 ≤ x) → (1 ≤ Mn) → (1 ≤ N) → (0 < θ) → (θ ≤ 1 / 4) →
      ((N : ℝ) ^ (2 : ℕ) ≤ (x : ℝ)) →
      (1 ≤ θ * (N : ℝ) ^ ((1 : ℝ) / 2)) →
      2 * (N : ℝ) ≤ θ ^ (2 : ℕ) * (Mn : ℝ) →
      (∀ i k, (Pa i k).M = (Mn : ℝ)) → (∀ i k, (Pa i k).N = a i) →
      (∀ i k, (Pa i k).τ = τ) →
      (∀ i, (N : ℝ) ≤ a i) → (∀ i, a i ≤ 2 * (N : ℝ)) →
      (∀ i u, 0 ≤ p i u) → (∀ i u, p i u ≤ 1) →
      (∀ i u, p i u ≠ 0 → a i < u ∧ u ≤ (1 + θ) * a i) →
      (∀ u, (N : ℝ) < u → u ≤ 2 * (N : ℝ) → (∑ i, p i u) ≤ 1) →
      (∀ k α, 0 ≤ q k α) → (∀ k α, q k α ≤ 1) → (∀ k, q k 0 = 0) →
      (∀ k α, q k α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ) →
      (∀ α, -Real.pi ≤ α → α ≤ Real.pi → (∑ k, q k (α - φ k)) = 1) →
      (∀ (i : Fin K) (k : Fin K') (z : GaussianInt),
        Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z ≠ 0 →
          Work.FIPlan.IsPrimitive z) →
      ((N : ℝ) ≤ (Mn : ℝ)) →
      (∑ i, ∑ k, ∑ mm ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter
          (fun m : ℕ => (m : ℝ) * a i < (x : ℝ)),
          ∑ w ∈ Work.FITop4.Red5.wSph mm, ∑ z ∈ Work.FITop4.Red5.primAnn (2 * N),
            2 * (if (mm : ℝ) * (Work.FIPlan.gnorm z : ℝ) > (x : ℝ) then (1 : ℝ) else 0)
              * ‖Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z
                  * Work.FITop3.Zc w z‖)
        ≤ c * θ * ((Mn : ℝ) * (N : ℝ)) ^ ((3 : ℝ) / 4) * (Real.log (x : ℝ)) ^ (100 : ℕ) := by
  obtain ⟨C2, hC2, hW⟩ := primAnn_rpow_weight
  exact window_T2_shell_of_crux_core Cc hcC hcrux C2 hC2 hW
    (fun x Mn θ hMn hθ z hprim hz1 =>
      window_T2_perz_of_crux_local Cc hcC hcrux x Mn θ hMn hθ z hprim hz1)
    window_T2_shell_arith

end

end Work.FITop4.Red5
