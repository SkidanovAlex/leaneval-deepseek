import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDCommon
import Submission.Work.HP.Sig2.CaseFDefs
import Submission.Work.HP.Sig2.NN_ge_add_two
import Submission.Work.HP.Sig2.omega_li
import Submission.Work.HP.MDEstimates.dmin_facts
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.MDEstimates.mu_sum_aux
import Submission.Work.HP.PairsAux
import Submission.Work.HP.MDEstimates.muXY_le
import Submission.Work.HP.Sig2.pairS0_R0_bound
import Submission.Work.HP.Sig2.CaseFSumBound
import Submission.Work.HP.MDEstimates.detGam_lower
import Submission.Work.HP.Sig2.caseF_arith

/-!
# Case F of the large-`μ` part of the second moment (Browning--Le Boudec--Sawin, Annals 2023)

`Work.HP.Sig2.Sigma2_caseF`: the contribution of the "case F" pairs (those with
`𝔡₂(x,y)³ ≤ 𝔡₃(x,y)‖x‖‖y‖`, so that `μ(x,y) = 3n²‖x‖‖y‖/𝔡₂²`) to the large-`μ` part of the
second moment is `≪ A^{N-2-1/3} B²`.

The proof: per pair, Lemma R0 with `R₀ = n-1` and the lower bound
`𝔡₂‖x‖^{d-1}‖y‖^{d-1} ≪ det Γ_{x,y}` give
`S*₀(Γ; B(A)) ≪ A^{N-n-1} R^{2(n-d)} 𝔡₂^{-(2n-1)} + A^{N-n-2}`, `R = B^{1/(n+1-d)}`.
Summing over the pairs, `Σ 𝔡₂^{-m} ≪ B^{4/(n+1-d)}(log B+1)^3` for every `m ≥ n-1` gives the
first term, while the cardinality `#T` is controlled by `𝔡₂(p)² < 3n²W²/A`, i.e.
`1 ≤ (3n²)^{(n-1)/2} W^{n-1} A^{-(n-1)/2} 𝔡₂(p)^{-(n-1)}`.  The final real-variable arithmetic is
`Work.HP.Sig2.caseF_arith`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MvPolynomial Finset
open scoped BigOperators

namespace Work.HP.Sig2

open Work.HP

/-! ## rpow helpers -/

lemma rpow_nat_sub (A : ℝ) {a b : ℕ} (h : b ≤ a) :
    A ^ (a - b) = A ^ ((a : ℝ) - (b : ℝ)) := by
  conv_lhs => rw [← Real.rpow_natCast A (a - b)]
  rw [Nat.cast_sub h]

/-- `dmin` is non-negative. -/
lemma dmin_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ) (S : Set (ι → ℤ)) :
    0 ≤ dmin r S := by
  rw [Work.HP.dmin]
  by_cases hne : {D : ℝ | ∃ L : Submodule ℤ (ι → ℤ), rk L = r ∧ S ⊆ L ∧ detL L = D}.Nonempty
  · exact le_csInf hne (fun D hD => by
      obtain ⟨L, _, _, rfl⟩ := hD
      exact Work.HP.detL_nonneg L)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sInf_empty]

/-! ## The per-pair sum bound in case F -/

theorem per_pair_sum_bound_F (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (hN : n + 2 ≤ NN d n)
    (Cdet : ℝ) (hCdet : 0 < Cdet)
    (hdet : ∀ x y : Fin (n + 1) → ℤ, IsPrim x → IsPrim y → LinearIndependent ℤ ![x, y] →
      dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) * eNorm x ^ (d - 1) * eNorm y ^ (d - 1)
        ≤ Cdet * detL (Gam d n x y)) :
    ∃ K : ℝ, 0 < K ∧ ∀ (A B : ℝ)
        (T : Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ))),
      1 ≤ A → 1 ≤ B → (∀ p ∈ T, p ∈ Omega d n B) →
      (∀ p ∈ T, A < muXY n p.1 p.2) →
      (∀ p ∈ T, dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) *
          dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ^ 2
          ≤ dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * (eNorm p.1 * eNorm p.2)) →
      (∑ p ∈ T, pairS0 d n A p)
        ≤ K * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1)
              * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ (2 * ((n : ℝ) - d))
              * (∑ p ∈ T, (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))) ^ (-(2 * (n : ℝ) - 1)))
            + A ^ ((NN d n : ℝ) - (n : ℝ) - 2) * (T.card : ℝ)) := by
  obtain ⟨K₀, hK₀pos, hK₀⟩ := pairS0_R0_bound d n hd hdn
  have hdf := MDEstimates.dmin_facts n (le_trans hd hdn)
  set C₁ : ℝ := K₀ * Cdet * (3 * (n : ℝ) ^ 2) ^ (NN d n) + K₀ with hC₁def
  have hC₁pos : 0 < C₁ := by rw [hC₁def]; positivity
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans hd hdn
  have h3n : (1 : ℝ) ≤ 3 * (n : ℝ) ^ 2 := by nlinarith [hn2R]
  refine ⟨C₁, hC₁pos, ?_⟩
  intro A B T hA1 hB1 hTΩ hTμ hTcase
  have hRN : n - 1 ≤ NN d n - 3 := by omega
  have hN1 : n + 1 ≤ NN d n := by omega
  have hN2 : n + 2 ≤ NN d n := hN
  have hpoint : ∀ p ∈ T, pairS0 d n A p ≤
      C₁ * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1)
            * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ (2 * ((n : ℝ) - d))
            * (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))) ^ (-(2 * (n : ℝ) - 1))
          + A ^ ((NN d n : ℝ) - (n : ℝ) - 2)) := by
    intro p hp
    set x := p.1 with hxdef
    set y := p.2 with hydef
    set d2 := dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) with hd2def
    set d3 := dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) with hd3def
    set X := eNorm x with hXdef
    set Y := eNorm y with hYdef
    set W := B ^ (1 / ((n : ℝ) + 1 - d)) with hWdef
    have hΩ := hTΩ p hp
    have hLI : LinearIndependent ℤ ![x, y] := li_of_mem_Omega d n B p hΩ
    have hXW : X ≤ W := hΩ.1.2
    have hYW : Y ≤ W := hΩ.2.1.2
    have hXnn : (0 : ℝ) ≤ X := eNorm_nonneg x
    have hYnn : (0 : ℝ) ≤ Y := eNorm_nonneg y
    have hWnn : (0 : ℝ) ≤ W := le_trans hXnn hXW
    have hcase := hTcase p hp
    have hd2pos : 0 < d2 := lt_of_lt_of_le zero_lt_one (hdf.1 x y hLI)
    have hd3pos : 0 < d3 := lt_of_lt_of_le zero_lt_one (hdf.2.2.1 x y hLI)
    have hd2le : d2 ≤ X * Y := hdf.2.1 x y hLI
    have hXYpos : 0 < X * Y := lt_of_lt_of_le hd2pos hd2le
    have hXYle : X * Y ≤ W ^ 2 := by nlinarith [hXW, hYW, hXnn, hYnn, hWnn]
    have hF' : d2 * d2 ^ 2 ≤ d3 * (X * Y) := by
      simpa only [← hd2def, ← hd3def, ← hXdef, ← hYdef] using hcase
    have hμle : d2 / d3 ≤ X * Y / d2 ^ 2 := by
      rw [div_le_div_iff₀ hd3pos (by positivity)]
      nlinarith [hF']
    have hμeq : muXY n x y = 3 * (n : ℝ) ^ 2 * (X * Y) / d2 ^ 2 := by
      simp only [muXY, ← hd2def, ← hd3def, ← hXdef, ← hYdef]
      rw [max_eq_right hμle]
      ring
    have hdet' := hdet x y hΩ.1.1 hΩ.2.1.1 hLI
    simp only [← hd2def, ← hXdef, ← hYdef] at hdet'
    have hxne : x ≠ 0 := MDEstimates.isPrim_ne_zero hΩ.1.1
    have hyne : y ≠ 0 := MDEstimates.isPrim_ne_zero hΩ.2.1.1
    have hXpos : 0 < X := eNorm_pos_of_ne_zero hxne
    have hYpos : 0 < Y := eNorm_pos_of_ne_zero hyne
    have hGpos : 0 < detL (Gam d n x y) := by
      have h1 : 0 < d2 * X ^ (d - 1) * Y ^ (d - 1) :=
        mul_pos (mul_pos hd2pos (pow_pos hXpos _)) (pow_pos hYpos _)
      exact pos_of_mul_pos_right (by linarith [h1, hdet'] : 0 < Cdet * detL (Gam d n x y))
        (le_of_lt hCdet)
    have hμpow : (muXY n x y) ^ (n - 1)
        = (3 * (n : ℝ) ^ 2) ^ (n - 1) * (X * Y) ^ (n - 1) / d2 ^ (2 * (n - 1)) := by
      rw [hμeq, div_pow, mul_pow, pow_mul]
    have hXYsplit : (X * Y) ^ (n - 1) = (X * Y) ^ (n - d) * (X ^ (d - 1) * Y ^ (d - 1)) := by
      rw [← mul_pow, ← pow_add]
      congr 1
      omega
    have hkey1 : (muXY n x y) ^ (n - 1) * d2 ^ (2 * n - 1)
        = (3 * (n : ℝ) ^ 2) ^ (n - 1) * (X * Y) ^ (n - 1) * d2 := by
      rw [hμpow, div_mul_eq_mul_div, mul_div_assoc, div_eq_mul_inv,
        ← pow_sub₀ d2 (ne_of_gt hd2pos) (by omega : 2 * (n - 1) ≤ 2 * n - 1),
        show 2 * n - 1 - 2 * (n - 1) = 1 by omega, pow_one]
    have hstep : d2 * (X ^ (d - 1) * Y ^ (d - 1)) ≤ Cdet * detL (Gam d n x y) := by
      linarith [hdet']
    have hkey2 : (3 * (n : ℝ) ^ 2) ^ (n - 1) * (X * Y) ^ (n - 1) * d2
        ≤ Cdet * (3 * (n : ℝ) ^ 2) ^ (n - 1) * (X * Y) ^ (n - d) * detL (Gam d n x y) := by
      rw [hXYsplit]
      calc (3 * (n : ℝ) ^ 2) ^ (n - 1) * ((X * Y) ^ (n - d) * (X ^ (d - 1) * Y ^ (d - 1))) * d2
          = (3 * (n : ℝ) ^ 2) ^ (n - 1) * (X * Y) ^ (n - d)
              * (d2 * (X ^ (d - 1) * Y ^ (d - 1))) := by ring
        _ ≤ (3 * (n : ℝ) ^ 2) ^ (n - 1) * (X * Y) ^ (n - d) * (Cdet * detL (Gam d n x y)) :=
            mul_le_mul_of_nonneg_left hstep (by positivity)
        _ = Cdet * (3 * (n : ℝ) ^ 2) ^ (n - 1) * (X * Y) ^ (n - d) * detL (Gam d n x y) := by
            ring
    have hfinal : (muXY n x y) ^ (n - 1) / detL (Gam d n x y)
        ≤ Cdet * (3 * (n : ℝ) ^ 2) ^ (n - 1) * (X * Y) ^ (n - d) / d2 ^ (2 * n - 1) := by
      rw [div_le_iff₀ hGpos, div_mul_eq_mul_div,
        le_div_iff₀ (by positivity : (0 : ℝ) < d2 ^ (2 * n - 1)), hkey1]
      exact hkey2
    have hXYpow2 : (X * Y) ^ (n - d) ≤ W ^ (2 * (n - d)) := by
      have h7 : (X * Y) ^ (n - d) ≤ (W ^ 2) ^ (n - d) :=
        pow_le_pow_left₀ (le_of_lt hXYpos) hXYle _
      rwa [← pow_mul] at h7
    have hfinal2 : (muXY n x y) ^ (n - 1) / detL (Gam d n x y)
        ≤ Cdet * (3 * (n : ℝ) ^ 2) ^ (n - 1) * W ^ (2 * (n - d)) * d2 ^ (-(2 * (n : ℝ) - 1)) := by
      have hcast : (((2 * n - 1 : ℕ)) : ℝ) = 2 * (n : ℝ) - 1 := by
        rw [Nat.cast_sub (show 1 ≤ 2 * n by omega)]
        push_cast
        ring
      calc (muXY n x y) ^ (n - 1) / detL (Gam d n x y)
          ≤ Cdet * (3 * (n : ℝ) ^ 2) ^ (n - 1) * (X * Y) ^ (n - d) / d2 ^ (2 * n - 1) := hfinal
        _ ≤ Cdet * (3 * (n : ℝ) ^ 2) ^ (n - 1) * W ^ (2 * (n - d)) / d2 ^ (2 * n - 1) := by
            refine div_le_div_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul_of_nonneg_left hXYpow2 (by positivity)
        _ = Cdet * (3 * (n : ℝ) ^ 2) ^ (n - 1) * W ^ (2 * (n - d))
              * d2 ^ (-(2 * (n : ℝ) - 1)) := by
            rw [div_eq_mul_inv, ← Real.rpow_natCast d2 (2 * n - 1), hcast,
              ← Real.rpow_neg (le_of_lt hd2pos)]
    have hW2 : W ^ (2 * (n - d)) = W ^ (2 * ((n : ℝ) - d)) := by
      rw [← Real.rpow_natCast W (2 * (n - d))]
      congr 1
      push_cast
      rw [Nat.cast_sub hdn]
    have hA1' : A ^ (NN d n - 2 - (n - 1)) = A ^ ((NN d n : ℝ) - (n : ℝ) - 1) := by
      rw [show NN d n - 2 - (n - 1) = NN d n - (n + 1) by omega, rpow_nat_sub A hN1]
      congr 1
      push_cast
      ring
    have hA2' : A ^ (NN d n - 3 - (n - 1)) = A ^ ((NN d n : ℝ) - (n : ℝ) - 2) := by
      rw [show NN d n - 3 - (n - 1) = NN d n - (n + 2) by omega, rpow_nat_sub A hN2]
      congr 1
      push_cast
      ring
    have hR0 := hK₀ A B p (n - 1) hΩ (le_trans (by norm_num) hA1) (le_of_lt (hTμ p hp)) hRN
    have hK0nn : (0 : ℝ) ≤ K₀ := le_of_lt hK₀pos
    have hlast : K₀ * (Cdet * (3 * (n : ℝ) ^ 2) ^ (n - 1))
          * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d))
            * d2 ^ (-(2 * (n : ℝ) - 1)))
        + K₀ * A ^ ((NN d n : ℝ) - (n : ℝ) - 2)
        ≤ C₁ * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d))
            * d2 ^ (-(2 * (n : ℝ) - 1)) + A ^ ((NN d n : ℝ) - (n : ℝ) - 2)) := by
      have hA2nn : (0 : ℝ) ≤ A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d))
          * d2 ^ (-(2 * (n : ℝ) - 1)) := by positivity
      have hA3nn : (0 : ℝ) ≤ A ^ ((NN d n : ℝ) - (n : ℝ) - 2) := by positivity
      have hKc : K₀ * (Cdet * (3 * (n : ℝ) ^ 2) ^ (n - 1)) ≤ C₁ := by
        have hle1 : K₀ * (Cdet * (3 * (n : ℝ) ^ 2) ^ (n - 1))
            ≤ K₀ * (Cdet * (3 * (n : ℝ) ^ 2) ^ (NN d n)) := by
          have : (3 * (n : ℝ) ^ 2) ^ (n - 1) ≤ (3 * (n : ℝ) ^ 2) ^ (NN d n) :=
            pow_le_pow_right₀ h3n (by omega)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this (le_of_lt hCdet))
            hK0nn
        have hle2 : K₀ * (Cdet * (3 * (n : ℝ) ^ 2) ^ (NN d n)) ≤ C₁ := by
          rw [hC₁def]; linarith
        linarith
      have hK0C₁ : K₀ ≤ C₁ := by
        rw [hC₁def]
        have h2 : (0 : ℝ) ≤ K₀ * Cdet * (3 * (n : ℝ) ^ 2) ^ (NN d n) := by positivity
        linarith
      have hb1 : K₀ * (Cdet * (3 * (n : ℝ) ^ 2) ^ (n - 1))
            * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d))
              * d2 ^ (-(2 * (n : ℝ) - 1))) ≤
          C₁ * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d))
              * d2 ^ (-(2 * (n : ℝ) - 1))) :=
        mul_le_mul_of_nonneg_right hKc hA2nn
      have hb2 : K₀ * A ^ ((NN d n : ℝ) - (n : ℝ) - 2)
          ≤ C₁ * A ^ ((NN d n : ℝ) - (n : ℝ) - 2) :=
        mul_le_mul_of_nonneg_right hK0C₁ hA3nn
      linarith [hb1, hb2]
    calc pairS0 d n A p
        ≤ K₀ * (A ^ (NN d n - 2 - (n - 1)) * (muXY n x y) ^ (n - 1) / detL (Gam d n x y)
            + A ^ (NN d n - 3 - (n - 1))) := hR0
      _ ≤ K₀ * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1)
            * (Cdet * (3 * (n : ℝ) ^ 2) ^ (n - 1) * W ^ (2 * (n - d))
              * d2 ^ (-(2 * (n : ℝ) - 1)))
            + A ^ ((NN d n : ℝ) - (n : ℝ) - 2)) := by
            rw [hA1', hA2']
            refine mul_le_mul_of_nonneg_left ?_ hK0nn
            have hstep2 : A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * (muXY n x y) ^ (n - 1)
                / detL (Gam d n x y)
                ≤ A ^ ((NN d n : ℝ) - (n : ℝ) - 1)
                  * (Cdet * (3 * (n : ℝ) ^ 2) ^ (n - 1) * W ^ (2 * (n - d))
                    * d2 ^ (-(2 * (n : ℝ) - 1))) := by
              rw [mul_div_assoc]
              exact mul_le_mul_of_nonneg_left hfinal2 (by positivity)
            exact add_le_add hstep2 le_rfl
      _ = K₀ * (Cdet * (3 * (n : ℝ) ^ 2) ^ (n - 1))
            * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d))
              * d2 ^ (-(2 * (n : ℝ) - 1)))
          + K₀ * A ^ ((NN d n : ℝ) - (n : ℝ) - 2) := by
            rw [hW2]
            ring
      _ ≤ C₁ * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d))
            * d2 ^ (-(2 * (n : ℝ) - 1)) + A ^ ((NN d n : ℝ) - (n : ℝ) - 2)) := hlast
      _ = C₁ * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1)
            * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ (2 * ((n : ℝ) - d))
            * (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))) ^ (-(2 * (n : ℝ) - 1))
          + A ^ ((NN d n : ℝ) - (n : ℝ) - 2)) := by
            rw [← hWdef, ← hd2def]
  refine le_trans (Finset.sum_le_sum hpoint) ?_
  have hkey : (∑ p ∈ T, C₁ * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1)
        * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ (2 * ((n : ℝ) - d))
        * (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))) ^ (-(2 * (n : ℝ) - 1))
        + A ^ ((NN d n : ℝ) - (n : ℝ) - 2)))
      = C₁ * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1)
        * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ (2 * ((n : ℝ) - d))
        * (∑ p ∈ T, (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))) ^ (-(2 * (n : ℝ) - 1)))
        + A ^ ((NN d n : ℝ) - (n : ℝ) - 2) * (T.card : ℝ)) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      nsmul_eq_mul]
    ring
  rw [hkey]


/-- Unfolded membership in `caseFset`. -/
lemma caseF_facts (d n : ℕ) {A B : ℝ} {p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)}
    (hp : p ∈ caseFset d n A B) :
    p ∈ Omega d n B ∧ IsPrim p.1 ∧ IsPrim p.2 ∧
    eNorm p.1 ≤ B ^ (1 / ((n : ℝ) + 1 - d)) ∧ eNorm p.2 ≤ B ^ (1 / ((n : ℝ) + 1 - d)) ∧
    LinearIndependent ℤ ![p.1, p.2] ∧
    ¬ (muXY n p.1 p.2 ≤ A) ∧
    dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ^ 2
      ≤ dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * (eNorm p.1 * eNorm p.2) := by
  simp only [caseFset, Set.mem_setOf_eq] at hp
  obtain ⟨hΩ, hμ, hF⟩ := hp
  simp only [Omega, Xi, Set.mem_setOf_eq] at hΩ
  obtain ⟨⟨hx, hxR⟩, ⟨hy, hyR⟩, hne, hne'⟩ := hΩ
  exact ⟨by simp only [Omega, Xi, Set.mem_setOf_eq]; exact ⟨⟨hx, hxR⟩, ⟨hy, hyR⟩, hne, hne'⟩,
    hx, hy, hxR, hyR, MDEstimates.linIndep_of_ne_pm hx hy hne hne', hμ, hF⟩

/-- `𝔡₂² < 3n²‖x‖‖y‖/A` in case F -/

lemma caseF_dmin2_lt (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) {A B : ℝ}
    {p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)} (hp : p ∈ caseFset d n A B) (hA : 0 < A) :
    (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))) ^ 2
      < 3 * (n : ℝ) ^ 2 * (eNorm p.1 * eNorm p.2) / A := by
  obtain ⟨hΩ, hx, hy, hxR, hyR, hLI, hμ, hF⟩ := caseF_facts d n hp
  set d2 := dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) with hd2def
  set d3 := dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) with hd3def
  set X := eNorm p.1 with hXdef
  set Y := eNorm p.2 with hYdef
  have hdf := MDEstimates.dmin_facts n (le_trans hd hdn)
  have hd2pos : 0 < d2 := lt_of_lt_of_le zero_lt_one (hdf.1 p.1 p.2 hLI)
  have hd3pos : 0 < d3 := lt_of_lt_of_le zero_lt_one (hdf.2.2.1 p.1 p.2 hLI)
  have hF' : d2 * d2 ^ 2 ≤ d3 * (X * Y) := by
    simpa only [← hd2def, ← hd3def, ← hXdef, ← hYdef] using hF
  have hμle : d2 / d3 ≤ X * Y / d2 ^ 2 := by
    rw [div_le_div_iff₀ hd3pos (by positivity)]
    nlinarith [hF']
  have hμeq : muXY n p.1 p.2 = 3 * (n : ℝ) ^ 2 * (X * Y) / d2 ^ 2 := by
    simp only [muXY, ← hd2def, ← hd3def, ← hXdef, ← hYdef]
    rw [max_eq_right hμle]
    ring
  have hlt : A < 3 * (n : ℝ) ^ 2 * (X * Y) / d2 ^ 2 := by
    rw [← hμeq]; exact lt_of_not_ge hμ
  rw [lt_div_iff₀ (by positivity : (0 : ℝ) < d2 ^ 2)] at hlt
  rw [lt_div_iff₀ hA]
  linarith [hlt]

/-- The cardinality bound in case F: every `p ∈ T` has `𝔡₂(p)² < 3n²‖x‖‖y‖/A ≤ 3n²W²/A`, so
`1 ≤ (3n²)^{(n-1)/2} W^{n-1} A^{-(n-1)/2} 𝔡₂(p)^{-(n-1)}`. -/
lemma card_le_dmin2 (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) {A B : ℝ} (hA : 0 < A) (hB1 : 1 ≤ B)
    (T : Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)))
    (hT : ∀ p ∈ T, p ∈ caseFset d n A B) :
    (T.card : ℝ) ≤ ((3 * (n : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2)
        * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ ((n : ℝ) - 1) * A ^ (-(((n : ℝ) - 1) / 2)))
      * ∑ p ∈ T, (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))) ^ (-((n : ℝ) - 1)) := by
  set W : ℝ := B ^ (1 / ((n : ℝ) + 1 - d)) with hWdef
  have hWnn : 0 ≤ W := by
    rw [hWdef]; exact Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ B) _
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans hd hdn
  set Δ : ℝ := (3 * (n : ℝ) ^ 2) ^ ((1 : ℝ) / 2) * W * A ^ (-((1 : ℝ) / 2)) with hΔdef
  have hΔnn : 0 ≤ Δ := by
    rw [hΔdef]; exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by nlinarith [hn2R] : (0:ℝ) ≤ 3*(n:ℝ)^2) _) hWnn)
      (Real.rpow_nonneg (le_of_lt hA) _)
  have hΔsq : Δ ^ 2 = 3 * (n : ℝ) ^ 2 * W ^ 2 / A := by
    rw [hΔdef, pow_two]
    have h1 : (3 * (n : ℝ) ^ 2) ^ ((1 : ℝ) / 2) * (3 * (n : ℝ) ^ 2) ^ ((1 : ℝ) / 2)
        = 3 * (n : ℝ) ^ 2 := by
      rw [← Real.rpow_add (by nlinarith [hn2R] : (0 : ℝ) < 3 * (n : ℝ) ^ 2)]
      norm_num
    have h2 : A ^ (-((1 : ℝ) / 2)) * A ^ (-((1 : ℝ) / 2)) = A ^ (-(1 : ℝ)) := by
      rw [← Real.rpow_add hA]
      norm_num
    rw [show (3 * (n : ℝ) ^ 2) ^ ((1 : ℝ) / 2) * W * A ^ (-((1 : ℝ) / 2))
          * ((3 * (n : ℝ) ^ 2) ^ ((1 : ℝ) / 2) * W * A ^ (-((1 : ℝ) / 2)))
        = ((3 * (n : ℝ) ^ 2) ^ ((1 : ℝ) / 2) * (3 * (n : ℝ) ^ 2) ^ ((1 : ℝ) / 2))
          * (W * W) * (A ^ (-((1 : ℝ) / 2)) * A ^ (-((1 : ℝ) / 2))) by ring,
      h1, h2, Real.rpow_neg (le_of_lt hA), Real.rpow_one]
    ring
  have hΔpow : Δ ^ ((n : ℝ) - 1) = (3 * (n : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2)
      * W ^ ((n : ℝ) - 1) * A ^ (-(((n : ℝ) - 1) / 2)) := by
    rw [hΔdef,
      Real.mul_rpow (mul_nonneg (Real.rpow_nonneg (by nlinarith [hn2R] : (0:ℝ) ≤ 3*(n:ℝ)^2) _) hWnn)
        (Real.rpow_nonneg (le_of_lt hA) _),
      Real.mul_rpow (Real.rpow_nonneg (by nlinarith [hn2R] : (0:ℝ) ≤ 3*(n:ℝ)^2) _) hWnn,
      ← Real.rpow_mul (by nlinarith [hn2R] : (0 : ℝ) ≤ 3 * (n : ℝ) ^ 2),
      ← Real.rpow_mul (le_of_lt hA)]
    ring_nf
  have hkey : ∀ p ∈ T, (1 : ℝ) ≤ (3 * (n : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2)
      * W ^ ((n : ℝ) - 1) * A ^ (-(((n : ℝ) - 1) / 2))
      * (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))) ^ (-((n : ℝ) - 1)) := by
    intro p hp
    have hpF := hT p hp
    obtain ⟨hΩ, hx, hy, hxR, hyR, hLI, hμ, hF⟩ := caseF_facts d n hpF
    set d2 := dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) with hd2def
    have hd2pos : 0 < d2 :=
      lt_of_lt_of_le zero_lt_one ((MDEstimates.dmin_facts n (le_trans hd hdn)).1 p.1 p.2 hLI)
    have hlt : d2 ^ 2 < 3 * (n : ℝ) ^ 2 * (eNorm p.1 * eNorm p.2) / A :=
      caseF_dmin2_lt d n hd hdn hpF hA
    have hXYle : eNorm p.1 * eNorm p.2 ≤ W ^ 2 := by
      have h1 : eNorm p.1 ≤ W := hxR
      have h2 : eNorm p.2 ≤ W := hyR
      nlinarith [h1, h2, eNorm_nonneg p.1, eNorm_nonneg p.2, hWnn]
    have hsq : d2 ^ 2 < Δ ^ 2 := by
      rw [hΔsq]
      have h1 : 3 * (n : ℝ) ^ 2 * (eNorm p.1 * eNorm p.2) / A ≤ 3 * (n : ℝ) ^ 2 * W ^ 2 / A :=
        div_le_div_of_nonneg_right (by nlinarith [hXYle]) (le_of_lt hA)
      linarith [hlt, h1]
    have hd2leΔ : d2 ≤ Δ := by
      have h := (sq_lt_sq.mp hsq)
      rw [abs_of_nonneg (le_of_lt hd2pos), abs_of_nonneg hΔnn] at h
      exact le_of_lt h
    have hm : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith [hn2R]
    have h1 : (1 : ℝ) ≤ (Δ / d2) ^ ((n : ℝ) - 1) := by
      refine Real.one_le_rpow ?_ hm
      rw [one_le_div hd2pos]
      exact hd2leΔ
    rw [Real.div_rpow hΔnn (le_of_lt hd2pos), div_eq_mul_inv,
      ← Real.rpow_neg (le_of_lt hd2pos), hΔpow] at h1
    exact h1
  have hcard1 : (T.card : ℝ) = ∑ p ∈ T, (1 : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hcard1, Finset.mul_sum]
  exact Finset.sum_le_sum hkey

theorem Sigma2_caseF (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (h22 : (d, n) ≠ (2, 2))
    (h33 : (d, n) ≠ (3, 3)) (h44 : (d, n) ≠ (4, 4)) :
    ∃ K B₀ : ℝ, 0 < K ∧ ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
      (∑ᶠ p ∈ {p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) | p ∈ Omega d n B ∧
          ¬ (muXY n p.1 p.2 ≤ A) ∧
          dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ^ 2
            ≤ dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * (eNorm p.1 * eNorm p.2)},
        pairS0 d n A p)
        ≤ K * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) * B ^ 2 := by
  have hn2 : 2 ≤ n := le_trans hd hdn
  have hn3 : 3 ≤ n := by
    rcases Nat.lt_or_ge n 3 with h | h
    · have hn : n = 2 := by omega
      have hd2 : d = 2 := by omega
      exact absurd (by simp [hn, hd2]) h22
    · exact h
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hN : n + 2 ≤ NN d n := NN_ge_add_two d n hd hdn
  obtain ⟨Cdet, hCdetpos, hCdet⟩ := MDEstimates.detGam_lower d n hd hn2
  obtain ⟨KF, hKFpos, hKF⟩ := per_pair_sum_bound_F d n hd hdn hN Cdet hCdetpos hCdet
  obtain ⟨Kd, hKdpos, hKd⟩ := cf_sum_dmin_rpow_le d n hd hn3
  set C : ℝ := KF * max 1 Kd * max 1 ((3 * (n : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2)) with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  obtain ⟨Kar, Bor, hKar, hBor, harith⟩ := caseF_arith d n hd hdn h22 h33 h44 C hCnn
  refine ⟨Kar, max Bor 8, hKar, ?_⟩
  intro A B hB hA hA2
  have hB8 : (8 : ℝ) ≤ B := le_trans (le_max_right _ _) hB
  have hB1 : (1 : ℝ) ≤ B := by linarith
  have hBpos : (0 : ℝ) < B := by linarith
  have hlogB1 : 1 ≤ Real.log B := by
    rw [Real.le_log_iff_exp_le hBpos]
    linarith [Real.exp_one_lt_d9]
  have hlogBpos : 0 < Real.log B := by linarith
  have hA1 : 1 ≤ A := by
    have h1 : (1 : ℝ) ≤ B / Real.log B := by
      rw [le_div_iff₀ hlogBpos]
      have := Real.log_le_self (le_of_lt hBpos)
      linarith
    linarith
  have hApos : 0 < A := by linarith
  set S := caseFset d n A B with hSdef
  have hSfin : S.Finite := caseFset_finite d n A B
  set T : Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) := hSfin.toFinset with hTdef
  have hTmem : ∀ p, p ∈ T ↔ p ∈ S := fun p => Set.Finite.mem_toFinset hSfin
  have hsum_eq : (∑ᶠ p ∈ S, pairS0 d n A p) = ∑ p ∈ T, pairS0 d n A p := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hSfin, hTdef]
  change (∑ᶠ p ∈ S, pairS0 d n A p) ≤ Kar * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) * B ^ 2
  rw [hsum_eq]
  have hST : ∀ p ∈ T, p ∈ caseFset d n A B := fun p hp => (hTmem p).mp hp
  have hΩT : ∀ p ∈ T, p ∈ Omega d n B := fun p hp => (caseF_facts d n (hST p hp)).1
  have hμT : ∀ p ∈ T, A < muXY n p.1 p.2 := fun p hp =>
    lt_of_not_ge (caseF_facts d n (hST p hp)).2.2.2.2.2.2.1
  have hFT : ∀ p ∈ T, dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))
      * dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ^ 2
      ≤ dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * (eNorm p.1 * eNorm p.2) := fun p hp =>
    (caseF_facts d n (hST p hp)).2.2.2.2.2.2.2
  have h1 := hKF A B T hA1 hB1 hΩT hμT hFT
  have hΩfin : (Omega d n B).Finite := (MDBasic.finite_sets d n A B (fun _ => True)).2.2
  have hTsubO : T ⊆ hΩfin.toFinset := fun p hp => (Set.Finite.mem_toFinset hΩfin).mpr (hΩT p hp)
  have hsum1Ω : (∑ p ∈ hΩfin.toFinset,
      (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))) ^ (-(2 * (n : ℝ) - 1)))
      ≤ Kd * B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3 := by
    have hh := hKd 2 le_rfl (by omega : 2 ≤ n + 1) (2 * (n : ℝ) - 1) B (by linarith [hn2R]) hB1
    rw [finsum_mem_eq_finite_toFinset_sum _ hΩfin] at hh
    rw [show (2 : ℝ) * (↑(2 : ℕ) : ℝ) / ((n : ℝ) + 1 - d) = 4 / ((n : ℝ) + 1 - d) by norm_num] at hh
    exact hh
  have hT1 : (∑ p ∈ T, (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))) ^ (-(2 * (n : ℝ) - 1)))
      ≤ Kd * B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hTsubO
      (fun i _ _ => Real.rpow_nonneg (dmin_nonneg 2 _) _)) hsum1Ω
  have hsum2Ω : (∑ p ∈ hΩfin.toFinset,
      (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))) ^ (-((n : ℝ) - 1)))
      ≤ Kd * B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3 := by
    have hh := hKd 2 le_rfl (by omega : 2 ≤ n + 1) ((n : ℝ) - 1) B le_rfl hB1
    rw [finsum_mem_eq_finite_toFinset_sum _ hΩfin] at hh
    rw [show (2 : ℝ) * (↑(2 : ℕ) : ℝ) / ((n : ℝ) + 1 - d) = 4 / ((n : ℝ) + 1 - d) by norm_num] at hh
    exact hh
  have hT2 : (∑ p ∈ T, (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))) ^ (-((n : ℝ) - 1)))
      ≤ Kd * B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hTsubO
      (fun i _ _ => Real.rpow_nonneg (dmin_nonneg 2 _) _)) hsum2Ω
  set W : ℝ := B ^ (1 / ((n : ℝ) + 1 - d)) with hWdef
  have hWnn : 0 ≤ W := by rw [hWdef]; exact Real.rpow_nonneg (le_of_lt hBpos) _
  set K2 : ℝ := (3 * (n : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2) * W ^ ((n : ℝ) - 1)
      * A ^ (-(((n : ℝ) - 1) / 2)) with hK2def
  have hK2nn : 0 ≤ K2 := by rw [hK2def]; positivity
  have hcard := card_le_dmin2 d n hd hdn hApos hB1 T hST
  have hcard' : (T.card : ℝ) ≤ K2 * (Kd * B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3) :=
    le_trans hcard (mul_le_mul_of_nonneg_left hT2 hK2nn)
  have hA2nn : (0 : ℝ) ≤ A ^ ((NN d n : ℝ) - (n : ℝ) - 2) := by positivity
  have hQnn : (0 : ℝ) ≤ B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3 := by positivity
  have hA2K2 : A ^ ((NN d n : ℝ) - (n : ℝ) - 2) * K2
      = (3 * (n : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2)
        * A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2) * W ^ ((n : ℝ) - 1) := by
    rw [hK2def,
      show A ^ ((NN d n : ℝ) - (n : ℝ) - 2)
          * ((3 * (n : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2) * W ^ ((n : ℝ) - 1)
            * A ^ (-(((n : ℝ) - 1) / 2)))
        = (3 * (n : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2) * W ^ ((n : ℝ) - 1)
          * (A ^ ((NN d n : ℝ) - (n : ℝ) - 2) * A ^ (-(((n : ℝ) - 1) / 2))) by ring,
      ← Real.rpow_add hApos]
    ring_nf
  have hcoef1 : KF * Kd ≤ C := by
    rw [hCdef]
    calc KF * Kd ≤ KF * max 1 Kd :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (le_of_lt hKFpos)
      _ ≤ KF * max 1 Kd * max 1 ((3 * (n : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2)) := by
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact le_mul_of_one_le_right (show (0 : ℝ) ≤ max 1 Kd from by positivity) (le_max_left _ _)
  have hcoef2 : KF * Kd * (3 * (n : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2) ≤ C := by
    rw [hCdef]
    calc KF * Kd * (3 * (n : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2)
        ≤ KF * max 1 Kd * (3 * (n : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_right _ _)
            (le_of_lt hKFpos)) (by positivity)
      _ ≤ KF * max 1 Kd * max 1 ((3 * (n : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2)) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
  have hmain : ∑ p ∈ T, pairS0 d n A p
      ≤ C * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d))
            + A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2) * W ^ ((n : ℝ) - 1))
          * (B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3) := by
    have hstep1 : ∑ p ∈ T, pairS0 d n A p
        ≤ KF * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d))
              * (Kd * B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3)
            + A ^ ((NN d n : ℝ) - (n : ℝ) - 2)
              * (K2 * (Kd * B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3))) := by
      refine le_trans h1 ?_
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hKFpos)
      exact add_le_add
        (mul_le_mul_of_nonneg_left hT1 (by positivity))
        (mul_le_mul_of_nonneg_left hcard' hA2nn)
    have hstep2 : KF * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d))
              * (Kd * B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3)
            + A ^ ((NN d n : ℝ) - (n : ℝ) - 2)
              * (K2 * (Kd * B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3)))
        = KF * Kd * ((A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d))
              + (3 * (n : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2)
                * A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2) * W ^ ((n : ℝ) - 1))
            * (B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3)) := by
      rw [show A ^ ((NN d n : ℝ) - (n : ℝ) - 2)
            * (K2 * (Kd * B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3))
          = (A ^ ((NN d n : ℝ) - (n : ℝ) - 2) * K2)
            * (Kd * B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3) by ring, hA2K2]
      ring
    have hstep3 : KF * Kd * ((A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d))
              + (3 * (n : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2)
                * A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2) * W ^ ((n : ℝ) - 1))
            * (B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3))
        ≤ C * ((A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d))
              + A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2) * W ^ ((n : ℝ) - 1))
            * (B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3)) := by
      have hX : (0 : ℝ) ≤ A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d)) := by
        positivity
      have hY : (0 : ℝ) ≤ A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2)
          * W ^ ((n : ℝ) - 1) := by positivity
      have hZ : (0 : ℝ) ≤ B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3 := hQnn
      have e1 : (KF * Kd) * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d)))
          * (B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3)
          ≤ C * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d)))
          * (B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef1 hX) hZ
      have e2 : (KF * Kd * (3 * (n : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2))
            * (A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2) * W ^ ((n : ℝ) - 1))
          * (B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3)
          ≤ C * (A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2) * W ^ ((n : ℝ) - 1))
          * (B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef2 hY) hZ
      linarith [e1, e2]
    calc ∑ p ∈ T, pairS0 d n A p
        ≤ KF * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d))
              * (Kd * B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3)
            + A ^ ((NN d n : ℝ) - (n : ℝ) - 2)
              * (K2 * (Kd * B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3))) := hstep1
      _ = KF * Kd * ((A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d))
              + (3 * (n : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2)
                * A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2) * W ^ ((n : ℝ) - 1))
            * (B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3)) := hstep2
      _ ≤ C * ((A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d))
              + A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2) * W ^ ((n : ℝ) - 1))
            * (B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3)) := hstep3
      _ = C * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d))
            + A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2) * W ^ ((n : ℝ) - 1))
          * (B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3) := by ring
  calc ∑ p ∈ T, pairS0 d n A p
      ≤ C * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d))
            + A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2) * W ^ ((n : ℝ) - 1))
          * (B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3) := hmain
    _ = C * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ (2 * ((n : ℝ) - d))
            * B ^ (4 / ((n : ℝ) + 1 - d))
          + A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2)
            * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ ((n : ℝ) - 1)
            * B ^ (4 / ((n : ℝ) + 1 - d)))
          * (Real.log B + 1) ^ 3 := by rw [← hWdef]; ring
    _ ≤ Kar * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) * B ^ 2 :=
        harith A B (le_trans (le_max_left _ _) hB) hA hA2

