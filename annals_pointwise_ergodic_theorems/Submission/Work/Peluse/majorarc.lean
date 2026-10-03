import Mathlib
import Submission.Work.Peluse.Fourier.dftOrthogonality
import Submission.Work.Peluse.Fourier.dftPlancherel
import Submission.Work.Peluse.Fourier.dftTriple
import Submission.Work.Peluse.corrReindex
import Submission.Work.Peluse.mapLinComb
import Submission.Work.Peluse.MajorArc.reindexToTriple
import Submission.Work.Peluse.MajorArc.dftBound
import Submission.Work.KMTAreas.A4.lip2PlainIW
import Submission.Work.KMTAreas.A4.lip2Amplify

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators
open Polynomial

namespace Work.Peluse

/-! ## Elementary helpers -/

/-- The distance to the nearest integer is at most the distance to any integer. -/
lemma distInt_le_abs_sub_int (x : ℝ) (m : ℤ) : distInt x ≤ |x - (m : ℝ)| := by
  rw [distInt]; exact round_le x m

/-- An l2-mass bound: a function bounded by 1 on the window [-N,N] has
sum of squared norms at most 2N+1. -/
lemma sum_normSq_le (N : ℕ) (f : ℤ → ℂ) (hb : ∀ x : ℤ, ‖f x‖ ≤ 1) :
    ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖f n‖ ^ 2 ≤ (((2 * N + 1 : ℕ) : ℝ)) := by
  have h1 : ∀ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖f n‖ ^ 2 ≤ (1 : ℝ) := by
    intro n _
    nlinarith [norm_nonneg (f n), hb n]
  calc ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖f n‖ ^ 2
      ≤ ∑ _n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1 : ℝ) := Finset.sum_le_sum h1
    _ = ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = (((2 * N + 1 : ℕ) : ℝ)) := by
        rw [Int.card_Icc]
        have h2 : (N : ℤ) + 1 - (-(N : ℤ)) = ((2 * N + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [h2, Int.toNat_natCast]

/-- The same bound for the weighted function eeG beta f. -/
lemma sum_normSq_eeG_le (N : ℕ) (f : ℤ → ℂ) (β : ℝ) (hb : ∀ x : ℤ, ‖f x‖ ≤ 1) :
    ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖eeG β f n‖ ^ 2 ≤ (((2 * N + 1 : ℕ) : ℝ)) := by
  have h1 : ∀ n : ℤ, ‖eeG β f n‖ ≤ 1 := by
    intro n
    rw [eeG, norm_mul, ee_norm, mul_one]
    exact hb n
  exact sum_normSq_le N (eeG β f) h1

/-- The windowed transform of the weight eeH M P beta is the Weyl sum
sum over y in [1,M] of ee (beta * P y - (k/L) * y). -/
lemma eeH_sum_window (M : ℕ) (P : Polynomial ℤ) (β : ℝ) (L k : ℕ) :
    (∑ y ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        eeH M P β y * ee (-((k : ℝ) * (y : ℝ)) / (L : ℝ)))
      = ∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ),
          ee (β * ((P.eval y : ℤ) : ℝ) - ((k : ℝ) / (L : ℝ)) * (y : ℝ)) := by
  have hsub : Finset.Icc (1 : ℤ) (M : ℤ) ⊆ Finset.Icc (-(M : ℤ)) (M : ℤ) := by
    intro y hy
    rw [Finset.mem_Icc] at hy ⊢
    constructor
    · have hMnn : (0 : ℤ) ≤ (M : ℤ) := Int.natCast_nonneg M
      omega
    · omega
  have hzero : ∀ y ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), y ∉ Finset.Icc (1 : ℤ) (M : ℤ) →
      eeH M P β y * ee (-((k : ℝ) * (y : ℝ)) / (L : ℝ)) = 0 := by
    intro y _ hy
    rw [eeH_apply_of_not_mem hy, zero_mul]
  rw [← Finset.sum_subset hsub hzero]
  apply Finset.sum_congr rfl
  intro y hy
  rw [eeH_apply_of_mem hy, ← ee_add]
  congr 1
  ring

/-- The inner u-sum is unchanged when the symmetric window [-N,N] is enlarged, since f0
vanishes off [-N,N]. -/
lemma sum_u_window_extend {N N' : ℕ} (hNN' : N ≤ N') (f₀ f₁ : ℤ → ℂ) (β : ℝ)
    (hs0 : SupportIn f₀ N) (y : ℤ) :
    (∑ u ∈ Finset.Icc (-(N' : ℤ)) (N' : ℤ), (f₀ u * ee (β * (u : ℝ))) * f₁ (u + y))
      = ∑ u ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (f₀ u * ee (β * (u : ℝ))) * f₁ (u + y) := by
  have hsub : Finset.Icc (-(N : ℤ)) (N : ℤ) ⊆ Finset.Icc (-(N' : ℤ)) (N' : ℤ) := by
    intro u hu
    rw [Finset.mem_Icc] at hu ⊢
    constructor <;> omega
  have hzero : ∀ u ∈ Finset.Icc (-(N' : ℤ)) (N' : ℤ), u ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) →
      (f₀ u * ee (β * (u : ℝ))) * f₁ (u + y) = 0 := by
    intro u _ hu
    have h2 : N < u.natAbs := by
      by_contra hcon
      push_neg at hcon
      exact hu (by
        rw [Finset.mem_Icc]
        have h3 : |u| ≤ (N : ℤ) := by
          rw [← Int.natCast_natAbs u]
          exact_mod_cast hcon
        rw [abs_le] at h3
        exact h3)
    rw [hs0 u h2, zero_mul, zero_mul]
  rw [← Finset.sum_subset hsub hzero]

/-! ## The main argument -/

theorem majorarc_core (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) : PeluseMajorArc P := by
  obtain ⟨C₁, hC₁pos, K₁, hIWd⟩ :=
    Work.KMTAreas.A4.lip2PlainIW_of_amp Work.KMTAreas.A4.lip2Amplify P.natDegree (by omega)
  set s : ℕ := P.leadingCoeff.natAbs with hsdef
  set K : ℕ := max K₁ 1 with hKdef
  set C' : ℝ := C₁ * (3 : ℝ) ^ K₁ * ((s : ℝ) + 1) + 1 with hC'def
  have hC'pos : 0 < C' := by rw [hC'def]; positivity
  have hC'one : 1 ≤ C' := by
    rw [hC'def]
    linarith [show (0 : ℝ) ≤ C₁ * (3 : ℝ) ^ K₁ * ((s : ℝ) + 1) by positivity]
  refine ⟨C', hC'pos, K, le_max_right _ _, ?_⟩
  intro N M f₀ f₁ β δ hdeg hN hM
  first
    | intro _ _ hδ0 hδ1 hs0 hs1 hb0 hb1 hcorr
    | intro hδ0 hδ1 hs0 hs1 hb0 hb1 hcorr
  by_cases hβ : β = 0
  · refine ⟨1, le_rfl, ?_, ?_⟩
    · have hδinv : (1 : ℝ) ≤ (δ⁻¹) ^ K :=
        one_le_pow₀ (by rw [one_le_inv₀ hδ0]; exact hδ1)
      have hprod : (1 : ℝ) * 1 ≤ C' * (δ⁻¹) ^ K :=
        mul_le_mul hC'one hδinv zero_le_one hC'pos.le
      simpa using hprod
    · have h0 : distInt (((1 : ℕ) : ℝ) * β) = 0 := by
        rw [hβ]; norm_num [distInt]
      rw [h0]
      exact le_of_lt (div_pos (mul_pos hC'pos (pow_pos (inv_pos.mpr hδ0) K))
        (pow_pos (by positivity : (0 : ℝ) < (M : ℝ)) _))
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hP0 : P ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (by omega : 1 < P.natDegree)
  have hlc0 : P.leadingCoeff ≠ 0 := by
    rw [Polynomial.leadingCoeff_ne_zero]; exact hP0
  have hs1' : 1 ≤ s := by
    rw [hsdef]
    exact Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hlc0)
  set L : ℕ := 2 * N + M + 1 with hLdef
  have hL1 : 1 ≤ L := by omega
  set S : ℂ := ∑ u ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ∑ y ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      eeG β f₀ u * eeH M P β y * f₁ (u + y) with hSdef
  set N' : ℕ := N + M with hN'def
  have hNN' : N ≤ N' := by omega
  have hAS : (∑' x : ℤ, dualFn M P f₀ f₁ x * Complex.exp (2 * Real.pi * Complex.I * β * x))
      = ((M : ℂ))⁻¹ * S := by
    have hre := Work.Peluse.corrReindex N' M P f₀ f₁ β hM (by omega)
      (hs0.mono hNN') (hs1.mono hNN')
    have hwin : ∀ y : ℤ,
        (∑ u ∈ Finset.Icc (-(N' : ℤ)) (N' : ℤ), (f₀ u * ee (β * (u : ℝ))) * f₁ (u + y))
          = ∑ u ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (f₀ u * ee (β * (u : ℝ))) * f₁ (u + y) :=
      fun y => sum_u_window_extend hNN' f₀ f₁ β hs0 y
    rw [hre]
    have hstep : (∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ), ee (β * ((P.eval y : ℤ) : ℝ)) *
          ∑ u ∈ Finset.Icc (-(N' : ℤ)) (N' : ℤ), (f₀ u * ee (β * (u : ℝ))) * f₁ (u + y))
        = ∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ), ee (β * ((P.eval y : ℤ) : ℝ)) *
          ∑ u ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (f₀ u * ee (β * (u : ℝ))) * f₁ (u + y) :=
      Finset.sum_congr rfl (fun y _ => by rw [hwin y])
    rw [hstep, Work.Peluse.MajorArc.reindexToTriple N M P f₀ f₁ β, hSdef]
    simp only [eeG]
  have hSnorm : δ * (N : ℝ) * (M : ℝ) ≤ ‖S‖ := by
    have h1 : δ * (N : ℝ) ≤ ‖((M : ℂ))⁻¹ * S‖ := by rw [← hAS]; exact hcorr
    have h2 : ‖((M : ℂ))⁻¹ * S‖ = ((M : ℝ))⁻¹ * ‖S‖ := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
    rw [h2] at h1
    have h3 : δ * (N : ℝ) * (M : ℝ) ≤ (((M : ℝ))⁻¹ * ‖S‖) * (M : ℝ) :=
      mul_le_mul_of_nonneg_right h1 hMpos.le
    have h4 : (((M : ℝ))⁻¹ * ‖S‖) * (M : ℝ) = ‖S‖ := by
      field_simp
    rw [h4] at h3
    exact h3
  have htriple := Work.Peluse.Fourier.dftTriple L N N M hL1 (by omega) (eeG β f₀) f₁
    (eeH M P β) (fun v hv => hs1 v hv)
  have hpa := Work.Peluse.Fourier.dftPlancherel L N hL1 (by omega) (eeG β f₀)
  have hpb := Work.Peluse.Fourier.dftPlancherel L N hL1 (by omega) f₁
  have hA2 : ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖eeG β f₀ n‖ ^ 2
      ≤ (((2 * N + 1 : ℕ) : ℝ)) := sum_normSq_eeG_le N f₀ β hb0
  have hB2 : ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖f₁ n‖ ^ 2
      ≤ (((2 * N + 1 : ℕ) : ℝ)) := sum_normSq_le N f₁ hb1
  obtain ⟨k0, hk0mem, hk0ineq⟩ :=
    Work.Peluse.MajorArc.dftBound L N N M hL1 (eeG β f₀) f₁ (eeH M P β)
      (((2 * N + 1 : ℕ) : ℝ)) (((2 * N + 1 : ℕ) : ℝ)) htriple hpa hpb hA2 hB2
  have hsqrt : Real.sqrt ((((2 * N + 1 : ℕ) : ℝ)) * (((2 * N + 1 : ℕ) : ℝ)))
      = (((2 * N + 1 : ℕ) : ℝ)) := Real.sqrt_mul_self (by positivity)
  have hSle : ‖S‖ ≤ ‖∑ y ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      eeH M P β y * ee (-((k0 : ℝ) * (y : ℝ)) / (L : ℝ))‖ * (((2 * N + 1 : ℕ) : ℝ)) := by
    rw [hSdef, ← hsqrt]
    exact hk0ineq
  have h2N3N : (((2 * N + 1 : ℕ) : ℝ)) ≤ 3 * (N : ℝ) := by
    have h : 2 * N + 1 ≤ 3 * N := by omega
    exact_mod_cast h
  have hweyl : δ * (M : ℝ) / 3
      ≤ ‖∑ y ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          eeH M P β y * ee (-((k0 : ℝ) * (y : ℝ)) / (L : ℝ))‖ := by
    set W : ℝ := ‖∑ y ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      eeH M P β y * ee (-((k0 : ℝ) * (y : ℝ)) / (L : ℝ))‖ with hWdef
    have hWS : δ * (N : ℝ) * (M : ℝ) ≤ W * (((2 * N + 1 : ℕ) : ℝ)) :=
      le_trans hSnorm (by rw [hWdef]; exact hSle)
    have hWN : W * (((2 * N + 1 : ℕ) : ℝ)) ≤ W * (3 * (N : ℝ)) :=
      mul_le_mul_of_nonneg_left h2N3N (by rw [hWdef]; positivity)
    have hkey : δ * (N : ℝ) * (M : ℝ) ≤ W * (3 * (N : ℝ)) := le_trans hWS hWN
    have hkey' : (δ * (M : ℝ)) * (N : ℝ) ≤ (3 * W) * (N : ℝ) := by
      linarith [hkey]
    have hfinal : δ * (M : ℝ) ≤ 3 * W := le_of_mul_le_mul_right hkey' hNpos
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
    linarith [hfinal]
  rw [eeH_sum_window M P β L k0] at hweyl
  set ξ : ℝ := (k0 : ℝ) / (L : ℝ) with hξdef
  set F : Polynomial ℝ := Polynomial.C β * P.map (Int.castRingHom ℝ)
    - Polynomial.C ξ * Polynomial.X with hFdef
  obtain ⟨hFdeg, hFlc, hFeval⟩ := Work.Peluse.mapLinComb P β ξ hβ hd
  have hMeq : ((((M : ℤ) - 1 : ℤ) : ℝ) + 1) = (M : ℝ) := by push_cast; ring
  have hmain : (δ / 3) * ((((M : ℤ) - 1 : ℤ) : ℝ) + 1)
      ≤ ‖∑ n ∈ Finset.Icc (1 : ℤ) (M : ℤ), (1 : ℂ) * ee (F.eval (n : ℝ))‖ := by
    rw [hMeq]
    have hsum : (∑ n ∈ Finset.Icc (1 : ℤ) (M : ℤ), (1 : ℂ) * ee (F.eval (n : ℝ)))
        = ∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ),
            ee (β * ((P.eval y : ℤ) : ℝ) - ((k0 : ℝ) / (L : ℝ)) * (y : ℝ)) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [one_mul, hFeval y, hξdef]
    rw [hsum]
    have : δ * (M : ℝ) / 3 = (δ / 3) * (M : ℝ) := by ring
    linarith [hweyl]
  obtain ⟨q, hq1, hqle, m, hm⟩ :=
    hIWd F (1 : ℂ) (1 : ℤ) (M : ℤ) (δ / 3) hFdeg (by norm_num) (by omega)
      (by positivity) (by linarith) hmain
  have hδinv1 : (1 : ℝ) ≤ δ⁻¹ := by rw [one_le_inv₀ hδ0]; exact hδ1
  have hpowδ : (δ⁻¹) ^ K₁ ≤ (δ⁻¹) ^ K := pow_le_pow_right₀ hδinv1 (le_max_left _ _)
  have hpow3 : ((δ / 3)⁻¹) ^ K₁ = (3 : ℝ) ^ K₁ * (δ⁻¹) ^ K₁ := by
    have h : (δ / 3)⁻¹ = 3 * δ⁻¹ := by
      rw [inv_div, div_eq_mul_inv]
    rw [h, mul_pow]
  have hC'big : C₁ * (3 : ℝ) ^ K₁ * ((s : ℝ) + 1) ≤ C' := by
    rw [hC'def]; linarith
  have hC'aa : C₁ * (3 : ℝ) ^ K₁ ≤ C' := by
    have h2 : C₁ * (3 : ℝ) ^ K₁ ≤ C₁ * (3 : ℝ) ^ K₁ * ((s : ℝ) + 1) := by
      have h3 : (1 : ℝ) ≤ (s : ℝ) + 1 := by
        have h4 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
        linarith
      nlinarith [show (0 : ℝ) ≤ C₁ * (3 : ℝ) ^ K₁ by positivity, h3]
    linarith [h2, hC'big]
  have hconst : C₁ * ((δ / 3)⁻¹) ^ K₁ ≤ C' * (δ⁻¹) ^ K := by
    rw [hpow3]
    calc C₁ * ((3 : ℝ) ^ K₁ * (δ⁻¹) ^ K₁) = (C₁ * (3 : ℝ) ^ K₁) * (δ⁻¹) ^ K₁ := by ring
      _ ≤ (C₁ * (3 : ℝ) ^ K₁) * (δ⁻¹) ^ K := mul_le_mul_of_nonneg_left hpowδ (by positivity)
      _ ≤ C' * (δ⁻¹) ^ K := mul_le_mul_of_nonneg_right hC'aa (by positivity)
  have hconsts : C₁ * (3 : ℝ) ^ K₁ * (s : ℝ) ≤ C' := by
    have hsnn : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
    nlinarith [hC'big, hsnn, show (0 : ℝ) < C₁ * (3 : ℝ) ^ K₁ by positivity]
  have ht1 : 1 ≤ q * s := Nat.mul_pos (by omega) (by omega)
  have ht2 : ((q * s : ℕ) : ℝ) ≤ C' * (δ⁻¹) ^ K := by
    have h1 : ((q * s : ℕ) : ℝ) = (q : ℝ) * (s : ℝ) := by push_cast; ring
    rw [h1]
    calc (q : ℝ) * (s : ℝ) ≤ (C₁ * ((δ / 3)⁻¹) ^ K₁) * (s : ℝ) :=
          mul_le_mul_of_nonneg_right hqle (Nat.cast_nonneg s)
      _ = (C₁ * (3 : ℝ) ^ K₁ * (s : ℝ)) * (δ⁻¹) ^ K₁ := by rw [hpow3]; ring
      _ ≤ (C₁ * (3 : ℝ) ^ K₁ * (s : ℝ)) * (δ⁻¹) ^ K :=
          mul_le_mul_of_nonneg_left hpowδ (by positivity)
      _ ≤ C' * (δ⁻¹) ^ K := mul_le_mul_of_nonneg_right hconsts (by positivity)
  have hm' : |(q : ℝ) * (β * ((P.leadingCoeff : ℤ) : ℝ)) - (m : ℝ)|
      ≤ C₁ * ((δ / 3)⁻¹) ^ K₁ / (M : ℝ) ^ P.natDegree := by
    have h := hm
    rw [hFlc, hMeq] at h
    exact h
  have hdist : distInt (((q * s : ℕ) : ℝ) * β)
      ≤ |(q : ℝ) * (β * ((P.leadingCoeff : ℤ) : ℝ)) - (m : ℝ)| := by
    rcases Int.natAbs_eq P.leadingCoeff with h | h
    · have hcast : ((q * s : ℕ) : ℝ) = (q : ℝ) * (s : ℝ) := by push_cast; ring
      have hlc : ((P.leadingCoeff : ℤ) : ℝ) = (s : ℝ) := by
        rw [h]
        simp only [Int.cast_natCast]
        rw [hsdef]
      rw [hcast, hlc]
      have hcomm : (q : ℝ) * (s : ℝ) * β = (q : ℝ) * (β * (s : ℝ)) := by ring
      rw [hcomm]
      exact distInt_le_abs_sub_int _ _
    · have hcast : ((q * s : ℕ) : ℝ) = (q : ℝ) * (s : ℝ) := by push_cast; ring
      have hlc : ((P.leadingCoeff : ℤ) : ℝ) = -((s : ℝ)) := by
        rw [h]
        simp only [Int.cast_neg, Int.cast_natCast]
        rw [hsdef]
      rw [hcast, hlc]
      have hneg : (q : ℝ) * (β * -((s : ℝ))) - (m : ℝ)
          = -(((q : ℝ) * (s : ℝ) * β) - (((-m : ℤ)) : ℝ)) := by push_cast; ring
      rw [hneg, abs_neg]
      exact distInt_le_abs_sub_int _ _
  refine ⟨q * s, ht1, ht2, ?_⟩
  have hMpow : (0 : ℝ) < (M : ℝ) ^ P.natDegree := pow_pos hMpos _
  have hlast : C₁ * ((δ / 3)⁻¹) ^ K₁ / (M : ℝ) ^ P.natDegree
      ≤ C' * (δ⁻¹) ^ K / (M : ℝ) ^ P.natDegree := by
    rw [div_le_iff₀ hMpow]
    have hd : C' * (δ⁻¹) ^ K / (M : ℝ) ^ P.natDegree * (M : ℝ) ^ P.natDegree
        = C' * (δ⁻¹) ^ K := by field_simp
    rw [hd]
    exact hconst
  exact le_trans hdist (le_trans hm' hlast)

theorem majorarc {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree) : Work.Peluse.PeluseMajorArc P :=
  majorarc_core P hd

end Work.Peluse
