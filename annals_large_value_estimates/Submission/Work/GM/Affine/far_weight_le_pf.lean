import Mathlib
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.psi1hat_decay
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.summable_int_inv_one_add_abs_pow

/-!
# The far weight is uniformly bounded (`Work.GM.Affine.far_weight_le_pf`)

This is the statement of `far_weight_le` in `far_mass_le_integral_Bsum.lean`: for every `M₃ ≥ 1`
and every `u : ℝ`,

`Σ'_ℓ [2/M₃ < |u - ℓ|] · ‖ψ̂₁(M₃(u-ℓ))‖² ≤ (2·3⁻² + 2 Σ_{j≥0} (1+j)⁻⁴ + 1) · C²`,

where `C = Classical.choose (psi1hat_decay K hK 2)`, so that `‖ψ̂₁ y‖ ≤ C (1+|y|)⁻²`.

The proof is the elementary lattice count indicated by the project lead: dropping the (positive)
indicator and using `psi1hat_decay K hK 2` gives
`‖ψ̂₁(M₃(u-ℓ))‖² ≤ C² (1+|u-ℓ|)⁻⁴` (because `M₃ ≥ 1`), and splitting `ℤ` at `⌊u⌋` bounds the
lattice sum by `1 + 2 Σ_{j≥0} (1+j)⁻⁴`; the extra `2·3⁻²` displayed on the right is pure slack
(only the `j = 0` terms need it, where `M₃|u-ℓ| > 2` gives `(1+|u-ℓ|)⁻⁴ ≤ 3⁻⁴ ≤ 3⁻²`).
-/

namespace Work.GM.Affine

open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-- `n ↦ 1/(n+1)^4` is summable on `ℕ`. -/
lemma pf_summable_inv_succ_pow4 : Summable (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)^4) := by
  have h : Summable (fun n : ℕ => (1:ℝ)/((n:ℝ))^4) :=
    (Real.summable_one_div_nat_pow (p := 4)).mpr (by norm_num)
  have h2 : Summable (fun n : ℕ => (1:ℝ)/((↑(n+1) : ℝ))^4) :=
    (summable_nat_add_iff (f := fun n : ℕ => (1:ℝ)/((n:ℝ))^4) 1).mpr h
  refine h2.congr (fun n => ?_)
  congr 1
  push_cast
  ring

/-- `ℓ ↦ 1/(1+|u-ℓ|)^4` is summable on `ℤ` (dominated by the `ℤ`-`p`-series after locating `u`
in the unit interval by `⌊u⌋`). -/
lemma pf_summable_inv_one_add_abs_sub_pow4 (u : ℝ) :
    Summable (fun ℓ : ℤ => (1:ℝ)/(1+|u-(ℓ:ℝ)|)^4) := by
  set m : ℤ := ⌊u⌋ with hmdef
  have hmle : (m:ℝ) ≤ u := by rw [hmdef]; exact Int.floor_le u
  have hmlt : u < (m:ℝ) + 1 := by rw [hmdef]; exact Int.lt_floor_add_one u
  have hbase : Summable (fun k : ℤ => (1:ℝ)/(1+|(k:ℝ)|)^4) :=
    summable_int_inv_one_add_abs_pow 4 (by norm_num)
  have hcomp : Summable (fun ℓ : ℤ => (1:ℝ)/(1+|(((m - ℓ : ℤ)):ℝ)|)^4) :=
    hbase.comp_injective (fun a b h => by omega)
  have hmaj : Summable (fun ℓ : ℤ => 16 * ((1:ℝ)/(1+|(((m - ℓ : ℤ)):ℝ)|)^4)) :=
    hcomp.mul_left 16
  refine Summable.of_nonneg_of_le (fun ℓ => by positivity) (fun ℓ => ?_) hmaj
  have hmm : (((m - ℓ : ℤ) : ℝ)) = (m:ℝ) - (ℓ:ℝ) := by push_cast; ring
  rw [hmm]
  have hkey : (1:ℝ) + |u - (ℓ:ℝ)| ≥ (1:ℝ)/2*(1+|(m:ℝ)-(ℓ:ℝ)|) := by
    rcases lt_or_ge ℓ (m+1) with h | h
    · have hle_int : ℓ ≤ m := by omega
      have hle : (ℓ:ℝ) ≤ (m:ℝ) := by exact_mod_cast hle_int
      have hle1 : 0 ≤ u - (ℓ:ℝ) := by linarith [hmle, hle]
      have hle2 : 0 ≤ (m:ℝ) - (ℓ:ℝ) := by linarith [hle]
      have h1 : |u - (ℓ:ℝ)| = u - (ℓ:ℝ) := by rw [abs_of_nonneg hle1]
      have h2 : |(m:ℝ) - (ℓ:ℝ)| = (m:ℝ) - (ℓ:ℝ) := by rw [abs_of_nonneg hle2]
      rw [h1, h2]; linarith [hle, hmle]
    · have hge : (m:ℝ) + 1 ≤ (ℓ:ℝ) := by exact_mod_cast h
      have huℓ : u - (ℓ:ℝ) < 0 := by linarith [hmlt, hge]
      have hmℓ : (m:ℝ) - (ℓ:ℝ) < 0 := by linarith [hge]
      have h1 : |u - (ℓ:ℝ)| = (ℓ:ℝ) - u := by rw [abs_of_neg huℓ]; ring
      have h2 : |(m:ℝ) - (ℓ:ℝ)| = (ℓ:ℝ) - (m:ℝ) := by rw [abs_of_neg hmℓ]; ring
      rw [h1, h2]; linarith [hge, hmlt]
  have hstep : (1:ℝ)/(1+|u-(ℓ:ℝ)|)^4 ≤ (1:ℝ)/((1:ℝ)/2*(1+|(m:ℝ)-(ℓ:ℝ)|))^4 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hkey 4)
  have hval2 : (1:ℝ)/((1:ℝ)/2*(1+|(m:ℝ)-(ℓ:ℝ)|))^4
      = 16 * ((1:ℝ)/(1+|(m:ℝ)-(ℓ:ℝ)|)^4) := by
    rw [show (1:ℝ)/2*(1+|(m:ℝ)-(ℓ:ℝ)|) = (1+|(m:ℝ)-(ℓ:ℝ)|)/2 by ring, div_pow, one_div_div]
    norm_num
    ring
  linarith [hstep, hval2.le, hval2.ge]

/-- **Elementary lattice estimate.**  Splitting `ℤ` at `⌊u⌋`, each side contributes at most
`Σ_{j≥0} (1+j)⁻⁴`: hence `Σ_{ℓ∈ℤ} (1+|u-ℓ|)⁻⁴ ≤ 1 + 2 Σ_{j≥0} (1+j)⁻⁴`. -/
lemma pf_tsum_inv_one_add_abs_sub_pow4_le (u : ℝ) :
    (∑' ℓ : ℤ, (1:ℝ)/(1+|u-(ℓ:ℝ)|)^4) ≤
      1 + 2*(∑' n : ℕ, (1:ℝ)/((n:ℝ)+1)^4) := by
  set m : ℤ := ⌊u⌋ with hmdef
  have hmle : (m:ℝ) ≤ u := by rw [hmdef]; exact Int.floor_le u
  have hmlt : u < (m:ℝ) + 1 := by rw [hmdef]; exact Int.lt_floor_add_one u
  set F : ℤ → ℝ := fun ℓ => (1:ℝ)/(1+|u-(ℓ:ℝ)|)^4 with hFdef
  set g : ℤ → ℝ := fun ℓ => F (m + ℓ) with hgdef
  have hS := pf_summable_inv_succ_pow4
  have hval : ∀ n : ℕ, (1:ℝ)/(((1:ℝ)/2*((n:ℝ)+1)))^4 = 16 * ((1:ℝ)/((n:ℝ)+1)^4) := by
    intro n
    rw [show ((1:ℝ)/2*((n:ℝ)+1)) = ((n:ℝ)+1)/2 by ring, div_pow, one_div_div]
    norm_num
    ring
  -- Both halves are dominated by `16 (n+1)⁻⁴`, which is summable.
  have hbnd1 : ∀ n : ℕ, g (n:ℤ) ≤ 16 * ((1:ℝ)/((n:ℝ)+1)^4) := by
    intro n
    have hcast : (((m + (n:ℤ) : ℤ) : ℝ)) = (m:ℝ) + (n:ℝ) := by push_cast; ring
    change F (m + (n:ℤ)) ≤ 16 * ((1:ℝ)/((n:ℝ)+1)^4)
    rw [hFdef]
    simp only [hcast]
    have hden : (1:ℝ) + |u - ((m:ℝ)+(n:ℝ))| ≥ (1:ℝ)/2*((n:ℝ)+1) := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp only [Nat.cast_zero, add_zero]
        have := abs_nonneg (u - (m:ℝ))
        linarith
      · have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
        have hpos : u - ((m:ℝ)+(n:ℝ)) < 0 := by linarith [hmlt, hn1]
        rw [abs_of_neg hpos]
        linarith [hmlt, hn1]
    have hstep : (1:ℝ)/(1+|u - ((m:ℝ)+(n:ℝ))|)^4
        ≤ (1:ℝ)/(((1:ℝ)/2*((n:ℝ)+1)))^4 := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      exact pow_le_pow_left₀ (by positivity) hden 4
    linarith [hstep, (hval n).le, (hval n).ge]
  have hbnd2 : ∀ n : ℕ, g (-(↑n+1)) ≤ 16 * ((1:ℝ)/((n:ℝ)+1)^4) := by
    intro n
    have hcast : (((m + (-(↑n+1)) : ℤ) : ℝ)) = (m:ℝ) - ((n:ℝ)+1) := by push_cast; ring
    change F (m + (-(↑n+1))) ≤ 16 * ((1:ℝ)/((n:ℝ)+1)^4)
    rw [hFdef]
    simp only [hcast]
    have hden : (1:ℝ) + |u - ((m:ℝ)-((n:ℝ)+1))| ≥ (1:ℝ)/2*((n:ℝ)+1) := by
      have hpos : 0 ≤ u - ((m:ℝ)-((n:ℝ)+1)) := by linarith [hmle]
      rw [abs_of_nonneg hpos]
      linarith [hmle]
    have hstep : (1:ℝ)/(1+|u - ((m:ℝ)-((n:ℝ)+1))|)^4
        ≤ (1:ℝ)/(((1:ℝ)/2*((n:ℝ)+1)))^4 := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      exact pow_le_pow_left₀ (by positivity) hden 4
    linarith [hstep, (hval n).le, (hval n).ge]
  have hg1 : Summable (fun n : ℕ => g (n:ℤ)) :=
    Summable.of_nonneg_of_le (fun n => by rw [hgdef]; simp only [hFdef]; positivity)
      hbnd1 (hS.mul_left 16)
  have hg2 : Summable (fun n : ℕ => g (-(↑n+1))) :=
    Summable.of_nonneg_of_le (fun n => by rw [hgdef]; simp only [hFdef]; positivity)
      hbnd2 (hS.mul_left 16)
  have hreindex : (∑' ℓ : ℤ, g ℓ) = ∑' ℓ : ℤ, F ℓ := by
    have h := Equiv.tsum_eq (Equiv.addRight m) F
    rw [← h]
    refine tsum_congr (fun c => ?_)
    change F (m + c) = F ((Equiv.addRight m) c)
    rw [show (Equiv.addRight m) c = c + m from rfl, add_comm]
  have hdecomp := tsum_of_nat_of_neg_add_one (f := g) hg1 hg2
  -- Sharper bounds on the two halves after peeling off the first term of the positive half.
  have hterm1 : ∀ n : ℕ, g (↑(n+1)) ≤ (1:ℝ)/((n:ℝ)+1)^4 := by
    intro n
    have hcast : (((m + (↑(n+1)) : ℤ) : ℝ)) = (m:ℝ) + ((n:ℝ)+1) := by push_cast; ring
    change F (m + (↑(n+1))) ≤ (1:ℝ)/((n:ℝ)+1)^4
    rw [hFdef]
    simp only [hcast]
    have hden : (1:ℝ) + |u - ((m:ℝ)+((n:ℝ)+1))| ≥ (1:ℝ) + (n:ℝ) := by
      have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      have hpos : u - ((m:ℝ)+((n:ℝ)+1)) < 0 := by linarith [hmlt, hn0]
      rw [abs_of_neg hpos]
      linarith [hmlt]
    have hstep : (1:ℝ)/(1+|u - ((m:ℝ)+((n:ℝ)+1))|)^4 ≤ (1:ℝ)/((1:ℝ)+(n:ℝ))^4 := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      exact pow_le_pow_left₀ (by positivity) hden 4
    have hv : (1:ℝ)/((1:ℝ)+(n:ℝ))^4 = (1:ℝ)/((n:ℝ)+1)^4 := by ring_nf
    linarith [hstep, hv.le, hv.ge]
  have hterm2 : ∀ n : ℕ, g (-(↑n+1)) ≤ (1:ℝ)/((n:ℝ)+1)^4 := by
    intro n
    have hcast : (((m + (-(↑n+1)) : ℤ) : ℝ)) = (m:ℝ) - ((n:ℝ)+1) := by push_cast; ring
    change F (m + (-(↑n+1))) ≤ (1:ℝ)/((n:ℝ)+1)^4
    rw [hFdef]
    simp only [hcast]
    have hden : (1:ℝ) + |u - ((m:ℝ)-((n:ℝ)+1))| ≥ (1:ℝ) + (n:ℝ) := by
      have hpos : 0 ≤ u - ((m:ℝ)-((n:ℝ)+1)) := by linarith [hmle]
      rw [abs_of_nonneg hpos]
      linarith [hmle]
    have hstep : (1:ℝ)/(1+|u - ((m:ℝ)-((n:ℝ)+1))|)^4 ≤ (1:ℝ)/((1:ℝ)+(n:ℝ))^4 := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      exact pow_le_pow_left₀ (by positivity) hden 4
    have hv : (1:ℝ)/((1:ℝ)+(n:ℝ))^4 = (1:ℝ)/((n:ℝ)+1)^4 := by ring_nf
    linarith [hstep, hv.le, hv.ge]
  have h0 : g ((0:ℕ):ℤ) ≤ 1 := by
    change F (m + (0:ℤ)) ≤ 1
    rw [hFdef]
    simp only [add_zero]
    have h1 : (1:ℝ) ≤ 1 + |u - (m:ℝ)| := by have := abs_nonneg (u - (m:ℝ)); linarith
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ h1
  have hsumm1 : Summable (fun n : ℕ => g (↑(n+1))) :=
    (summable_nat_add_iff (f := fun k : ℕ => g (↑k)) 1).mpr hg1
  have htail : (∑' n : ℕ, g (↑(n+1))) ≤ ∑' n : ℕ, (1:ℝ)/((n:ℝ)+1)^4 :=
    Summable.tsum_le_tsum hterm1 hsumm1 hS
  have hpos : (∑' n : ℕ, g (n:ℤ)) ≤ 1 + (∑' n : ℕ, (1:ℝ)/((n:ℝ)+1)^4) := by
    rw [Summable.tsum_eq_zero_add hg1]
    exact add_le_add h0 htail
  have hneg : (∑' n : ℕ, g (-(↑n+1))) ≤ ∑' n : ℕ, (1:ℝ)/((n:ℝ)+1)^4 :=
    Summable.tsum_le_tsum hterm2 hg2 hS
  calc (∑' ℓ : ℤ, (1:ℝ)/(1+|u-(ℓ:ℝ)|)^4) = ∑' ℓ : ℤ, F ℓ := rfl
    _ = ∑' ℓ : ℤ, g ℓ := hreindex.symm
    _ = (∑' n : ℕ, g (n:ℤ)) + (∑' n : ℕ, g (-(↑n+1))) := hdecomp
    _ ≤ (1 + (∑' n : ℕ, (1:ℝ)/((n:ℝ)+1)^4)) + (∑' n : ℕ, (1:ℝ)/((n:ℝ)+1)^4) :=
        add_le_add hpos hneg
    _ = 1 + 2*(∑' n : ℕ, (1:ℝ)/((n:ℝ)+1)^4) := by ring

/-- The far weight is uniformly bounded (the statement of `far_weight_le` in far_mass_le_integral_Bsum.lean). -/
theorem far_weight_le_pf {K M₃ : ℝ} (hK : 0 < K) (hM₃ : 1 ≤ M₃) (u : ℝ) :
    (∑' ℓ : ℤ, (if 2 / M₃ < |u - (ℓ : ℝ)| then ‖psi1hat K (M₃ * (u - (ℓ : ℝ)))‖ ^ 2
      else 0)) ≤ (2 * 3 ^ (-(2:ℤ)) + 2 * (∑' j : ℕ, (1 + (j:ℝ)) ^ (-(4:ℤ))) + 1)
        * (Classical.choose (psi1hat_decay K hK 2)) ^ 2 := by
  set C : ℝ := Classical.choose (psi1hat_decay K hK 2) with hCdef
  have hCpos : 0 < C := by
    rw [hCdef]; exact (Classical.choose_spec (psi1hat_decay K hK 2)).1
  have hdec : ∀ y : ℝ, ‖psi1hat K y‖ ≤ C/(1+|y|)^2 := by
    rw [hCdef]; exact (Classical.choose_spec (psi1hat_decay K hK 2)).2
  have hM₃pos : 0 < M₃ := lt_of_lt_of_le zero_lt_one hM₃
  set S : ℝ := ∑' j : ℕ, (1 + (j:ℝ)) ^ (-(4:ℤ)) with hSdef
  -- Pointwise: dropping the indicator and using `M₃ ≥ 1`.
  have hterm : ∀ ℓ : ℤ, (if 2/M₃ < |u-(ℓ:ℝ)| then ‖psi1hat K (M₃*(u-(ℓ:ℝ)))‖^2 else 0)
      ≤ C^2 * ((1:ℝ)/(1+|u-(ℓ:ℝ)|)^4) := by
    intro ℓ
    by_cases h : 2/M₃ < |u-(ℓ:ℝ)|
    · rw [if_pos h]
      have hy : |M₃*(u-(ℓ:ℝ))| = M₃*|u-(ℓ:ℝ)| := by rw [abs_mul, abs_of_pos hM₃pos]
      have h2 : ‖psi1hat K (M₃*(u-(ℓ:ℝ)))‖^2 ≤ (C/(1+|M₃*(u-(ℓ:ℝ))|)^2)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hdec _) 2
      have h3 : (C/(1+|M₃*(u-(ℓ:ℝ))|)^2)^2 = C^2/(1+M₃*|u-(ℓ:ℝ)|)^4 := by
        rw [hy, div_pow, ← pow_mul]
      have h5 : (1+|u-(ℓ:ℝ)|)^4 ≤ (1+M₃*|u-(ℓ:ℝ)|)^4 := by
        apply pow_le_pow_left₀ (by positivity)
        have hd : 0 ≤ |u - (ℓ:ℝ)| := abs_nonneg _
        nlinarith [hd, hM₃]
      have h6 : C^2/(1+M₃*|u-(ℓ:ℝ)|)^4 ≤ C^2 * ((1:ℝ)/(1+|u-(ℓ:ℝ)|)^4) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        exact mul_le_mul_of_nonneg_left h5 (sq_nonneg C)
      calc ‖psi1hat K (M₃*(u-(ℓ:ℝ)))‖^2 ≤ (C/(1+|M₃*(u-(ℓ:ℝ))|)^2)^2 := h2
        _ = C^2/(1+M₃*|u-(ℓ:ℝ)|)^4 := h3
        _ ≤ C^2 * ((1:ℝ)/(1+|u-(ℓ:ℝ)|)^4) := h6
    · rw [if_neg h]
      positivity
  have hsumm0 : Summable (fun ℓ : ℤ => (1:ℝ)/(1+|u-(ℓ:ℝ)|)^4) :=
    pf_summable_inv_one_add_abs_sub_pow4 u
  have hsummC : Summable (fun ℓ : ℤ => C^2 * ((1:ℝ)/(1+|u-(ℓ:ℝ)|)^4)) :=
    Summable.mul_left (C^2) hsumm0
  have hLHSsumm : Summable (fun ℓ : ℤ =>
      (if 2/M₃ < |u-(ℓ:ℝ)| then ‖psi1hat K (M₃*(u-(ℓ:ℝ)))‖^2 else 0)) :=
    Summable.of_nonneg_of_le
      (f := fun ℓ : ℤ => C^2 * ((1:ℝ)/(1+|u-(ℓ:ℝ)|)^4))
      (g := fun ℓ : ℤ => (if 2/M₃ < |u-(ℓ:ℝ)| then ‖psi1hat K (M₃*(u-(ℓ:ℝ)))‖^2 else 0))
      (fun ℓ => by
        by_cases h : 2/M₃ < |u-(ℓ:ℝ)|
        · rw [if_pos h]; positivity
        · exact le_of_eq (if_neg h).symm)
      hterm hsummC
  have hstep1 : (∑' ℓ : ℤ, (if 2/M₃ < |u-(ℓ:ℝ)| then ‖psi1hat K (M₃*(u-(ℓ:ℝ)))‖^2 else 0))
      ≤ ∑' ℓ : ℤ, C^2 * ((1:ℝ)/(1+|u-(ℓ:ℝ)|)^4) :=
    Summable.tsum_le_tsum hterm hLHSsumm hsummC
  -- Rewrite `S` against the `ℕ`-indexed form used by the lattice estimate.
  have hconv : (∑' n : ℕ, (1:ℝ)/((n:ℝ)+1)^4) = S := by
    rw [hSdef]
    refine tsum_congr (fun n => ?_)
    rw [zpow_neg, show (4:ℤ) = ((4:ℕ):ℤ) from rfl, zpow_natCast, inv_eq_one_div]
    ring
  have hle : C^2 * (1 + 2*S) ≤ (2*3^(-(2:ℤ)) + 2*S + 1)*C^2 := by
    have h3 : (0:ℝ) ≤ 3^(-(2:ℤ)) := zpow_nonneg (by norm_num) (-(2:ℤ))
    have key : (2*3^(-(2:ℤ)) + 2*S + 1)*C^2 - C^2*(1+2*S) = (2*3^(-(2:ℤ)))*C^2 := by ring
    have hkey2 : 0 ≤ (2*3^(-(2:ℤ)))*C^2 := mul_nonneg (by linarith) (sq_nonneg C)
    linarith [key, hkey2]
  calc (∑' ℓ : ℤ, (if 2/M₃ < |u-(ℓ:ℝ)| then ‖psi1hat K (M₃*(u-(ℓ:ℝ)))‖^2 else 0))
      ≤ ∑' ℓ : ℤ, C^2 * ((1:ℝ)/(1+|u-(ℓ:ℝ)|)^4) := hstep1
    _ = C^2 * (∑' ℓ : ℤ, (1:ℝ)/(1+|u-(ℓ:ℝ)|)^4) := tsum_mul_left
    _ ≤ C^2 * (1 + 2*S) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg C)
        calc (∑' ℓ : ℤ, (1:ℝ)/(1+|u-(ℓ:ℝ)|)^4)
            ≤ 1 + 2*(∑' n : ℕ, (1:ℝ)/((n:ℝ)+1)^4) := pf_tsum_inv_one_add_abs_sub_pow4_le u
          _ = 1 + 2*S := by rw [hconv]
    _ ≤ (2*3^(-(2:ℤ)) + 2*S + 1)*C^2 := hle


end

end Work.GM.Affine
