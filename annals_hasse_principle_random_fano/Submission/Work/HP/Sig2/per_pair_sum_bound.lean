import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDCommon
import Submission.Work.HP.Sig2.omega_li
import Submission.Work.HP.Sig2.pairS0_R0_bound
import Submission.Work.HP.Sig2.mu_div_det_le
import Submission.Work.HP.MDEstimates.muXY_le
import Submission.Work.HP.MDEstimates.dmin_facts
import Submission.Work.HP.six_le_NN

/-!
# Summing the Lemma-R0 bound over a set of pairs

For a finite set `T` of Case-I pairs in `Omega d n B` with `A < muXY`, the Lemma-R0 bound
`pairS0_R0_bound` combined with the Case-I conversion `mu_div_det_le` gives, for `d ≤ R ≤ N-3`,

`∑_{p ∈ T} pairS0 d n A p ≤ K ( A^{N-2-R} W^{2(R-d)} ∑_{p ∈ T} 𝔡₃(p)^{-R} + A^{N-3-R} #T )`,

where `W = B^{1/(n+1-d)}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.HP.Sig2

open Work.HP

theorem per_pair_sum_bound (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n)
    (Cdet : ℝ) (hCdet : 0 < Cdet)
    (hdet : ∀ x y : Fin (n + 1) → ℤ, IsPrim x → IsPrim y → LinearIndependent ℤ ![x, y] →
      Cdet * dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) * eNorm x ^ (d - 1) * eNorm y ^ (d - 1)
        ≤ detL (Gam d n x y)) :
    ∃ K : ℝ, 0 < K ∧ ∀ (A B : ℝ) (R : ℕ)
        (T : Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ))),
      d ≤ R → R ≤ NN d n - 3 → 1 ≤ A →
      (∀ p ∈ T, p ∈ Omega d n B) →
      (∀ p ∈ T, A < muXY n p.1 p.2) →
      (∀ p ∈ T, ¬ (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) *
          dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ^ 2
          ≤ dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * (eNorm p.1 * eNorm p.2))) →
      (∑ p ∈ T, pairS0 d n A p)
        ≤ K * (A ^ (NN d n - 2 - R) * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ (2 * (R - d)) *
              (∑ p ∈ T, (dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))) ^ (-(R : ℝ)))
            + A ^ (NN d n - 3 - R) * T.card) := by
  obtain ⟨K₀, hK₀pos, hK₀⟩ := pairS0_R0_bound d n hd hdn
  have hdf := MDEstimates.dmin_facts n (by omega)
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
  have h3n1 : (1 : ℝ) ≤ 3 * (n : ℝ) ^ 2 := by nlinarith [hn2]
  refine ⟨K₀ * ((3 * (n : ℝ) ^ 2) ^ (NN d n) / Cdet + 1) + K₀ + 1, by positivity, ?_⟩
  intro A B R T hdR hRN hA1 hTΩ hTμ hTcase
  set W : ℝ := B ^ (1 / ((n : ℝ) + 1 - d)) with hWdef
  set Kc : ℝ := (3 * (n : ℝ) ^ 2) ^ (NN d n) / Cdet + 1 with hKcdef
  set K : ℝ := K₀ * ((3 * (n : ℝ) ^ 2) ^ (NN d n) / Cdet + 1) + K₀ + 1 with hKdef
  have hKcK : K₀ * Kc ≤ K := by
    rw [hKdef, hKcdef]
    linarith [hK₀pos]
  have hK0K : K₀ ≤ K := by
    rw [hKdef]
    have : (0:ℝ) ≤ K₀ * ((3 * (n : ℝ) ^ 2) ^ (NN d n) / Cdet) :=
      mul_nonneg hK₀pos.le (div_nonneg (by positivity) hCdet.le)
    linarith
  have hpoint : ∀ p ∈ T, pairS0 d n A p ≤
      K * (A ^ (NN d n - 2 - R) * W ^ (2 * (R - d)) *
          (dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))) ^ (-(R : ℝ)))
      + K * A ^ (NN d n - 3 - R) := by
    intro p hp
    set x := p.1 with hxdef
    set y := p.2 with hydef
    set X := eNorm x with hXdef
    set Y := eNorm y with hYdef
    have hΩ := hTΩ p hp
    have hLI : LinearIndependent ℤ ![x, y] := li_of_mem_Omega d n B p hΩ
    have hxW : X ≤ W := hΩ.1.2
    have hyW : Y ≤ W := hΩ.2.1.2
    have hW0 : 0 ≤ W := le_trans (eNorm_nonneg x) hxW
    have hd2pos : 0 < dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) :=
      lt_of_lt_of_le zero_lt_one (hdf.1 x y hLI)
    have hd3pos : 0 < dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) :=
      lt_of_lt_of_le zero_lt_one (hdf.2.2.1 x y hLI)
    have hd2le : dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ≤ X * Y := hdf.2.1 x y hLI
    have hdet := hdet x y hΩ.1.1 hΩ.2.1.1 hLI
    have hcase := hTcase p hp
    have hmudiv := mu_div_det_le d n hd Cdet hCdet R hdR x y W hW0 hd2pos hd3pos hd2le
      hxW hyW hdet hcase
    have hR0 := hK₀ A B p R hΩ hA1 (le_of_lt (hTμ p hp)) hRN
    have h3nR : (3 * (n : ℝ) ^ 2) ^ R ≤ (3 * (n : ℝ) ^ 2) ^ (NN d n) := by
      have hle : ((R : ℕ) : ℝ) ≤ ((NN d n : ℕ) : ℝ) := by
        exact_mod_cast (le_trans hRN (Nat.sub_le (NN d n) 3))
      have h := Real.rpow_le_rpow_of_exponent_le h3n1 hle
      simpa only [Real.rpow_natCast] using h
    have hA2nn : (0:ℝ) ≤ A ^ (NN d n - 2 - R) := by positivity
    have hB2nn : (0:ℝ) ≤ W ^ (2 * (R - d)) := by positivity
    have hd3nn : (0:ℝ) ≤ (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))) ^ (-(R : ℝ)) :=
      Real.rpow_nonneg hd3pos.le _
    have hQ : (0:ℝ) ≤ A ^ (NN d n - 2 - R) * W ^ (2 * (R - d)) *
        (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))) ^ (-(R : ℝ)) :=
      mul_nonneg (mul_nonneg hA2nn hB2nn) hd3nn
    have hface : (3 * (n : ℝ) ^ 2) ^ R / Cdet ≤ Kc := by
      have h1 : (3 * (n : ℝ) ^ 2) ^ R / Cdet ≤ (3 * (n : ℝ) ^ 2) ^ (NN d n) / Cdet :=
        div_le_div_of_nonneg_right h3nR hCdet.le
      rw [hKcdef]
      linarith
    have hbound : A ^ (NN d n - 2 - R) * (muXY n x y) ^ R / detL (Gam d n x y)
        ≤ Kc * (A ^ (NN d n - 2 - R) * W ^ (2 * (R - d)) *
            (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))) ^ (-(R : ℝ))) := by
      have h1 : A ^ (NN d n - 2 - R) * ((muXY n x y) ^ R / detL (Gam d n x y))
          ≤ A ^ (NN d n - 2 - R) * ((3 * (n : ℝ) ^ 2) ^ R * W ^ (2 * (R - d)) *
              (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))) ^ (-(R : ℝ)) / Cdet) :=
        mul_le_mul_of_nonneg_left hmudiv hA2nn
      have h2 : A ^ (NN d n - 2 - R) * ((3 * (n : ℝ) ^ 2) ^ R * W ^ (2 * (R - d)) *
            (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))) ^ (-(R : ℝ)) / Cdet)
          = ((3 * (n : ℝ) ^ 2) ^ R / Cdet) * (A ^ (NN d n - 2 - R) * W ^ (2 * (R - d)) *
              (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))) ^ (-(R : ℝ))) := by ring
      calc A ^ (NN d n - 2 - R) * (muXY n x y) ^ R / detL (Gam d n x y)
          = A ^ (NN d n - 2 - R) * ((muXY n x y) ^ R / detL (Gam d n x y)) := by ring
        _ ≤ A ^ (NN d n - 2 - R) * ((3 * (n : ℝ) ^ 2) ^ R * W ^ (2 * (R - d)) *
              (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))) ^ (-(R : ℝ)) / Cdet) := h1
        _ = ((3 * (n : ℝ) ^ 2) ^ R / Cdet) * (A ^ (NN d n - 2 - R) * W ^ (2 * (R - d)) *
              (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))) ^ (-(R : ℝ))) := h2
        _ ≤ Kc * (A ^ (NN d n - 2 - R) * W ^ (2 * (R - d)) *
              (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))) ^ (-(R : ℝ))) :=
            mul_le_mul_of_nonneg_right hface hQ
    calc pairS0 d n A p
        ≤ K₀ * (A ^ (NN d n - 2 - R) * (muXY n x y) ^ R / detL (Gam d n x y)
            + A ^ (NN d n - 3 - R)) := hR0
      _ ≤ K₀ * (Kc * (A ^ (NN d n - 2 - R) * W ^ (2 * (R - d)) *
              (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))) ^ (-(R : ℝ)))
            + A ^ (NN d n - 3 - R)) := by
          have hsum := add_le_add_right hbound (A ^ (NN d n - 3 - R))
          exact mul_le_mul_of_nonneg_left (by linarith [hsum, hbound]) hK₀pos.le
      _ = K₀ * Kc * (A ^ (NN d n - 2 - R) * W ^ (2 * (R - d)) *
              (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))) ^ (-(R : ℝ)))
            + K₀ * A ^ (NN d n - 3 - R) := by ring
      _ ≤ K * (A ^ (NN d n - 2 - R) * W ^ (2 * (R - d)) *
              (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))) ^ (-(R : ℝ)))
            + K * A ^ (NN d n - 3 - R) := by
          have h1 := mul_le_mul_of_nonneg_right hKcK hQ
          have h2 := mul_le_mul_of_nonneg_right hK0K (by positivity : (0:ℝ) ≤ A ^ (NN d n - 3 - R))
          linarith [h1, h2]
      _ = K * (A ^ (NN d n - 2 - R) * W ^ (2 * (R - d)) *
              (dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))) ^ (-(R : ℝ)))
            + K * A ^ (NN d n - 3 - R) := by rw [hxdef, hydef]
  refine le_trans (Finset.sum_le_sum hpoint) ?_
  refine le_of_eq ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  ring

end Work.HP.Sig2
