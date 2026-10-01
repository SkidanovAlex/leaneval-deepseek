import Mathlib
import Submission.Work.ZeroDensity.Ingham.AfeProof.zetaAfeResidual
import Submission.Work.ZeroDensity.Ingham.norm_zetaChi_critical
import Submission.Work.ZeroDensity.Ingham.zetaAfeDefs
import Submission.Work.ZeroDensity.Ingham.AfeSelf.Defs

namespace Work.ZeroDensity.Ingham.AfeProof

open scoped BigOperators

/-!
# Elementary pieces for the sharp approximate functional equation

This file contains the final assembly of `Work.ZeroDensity.Ingham.AfeProof.zetaAfeSharp`
from the balanced residual `Work.ZeroDensity.Ingham.AfeProof.zetaAfeResidual`.

Three elementary facts are used, and each is proved below from scratch:

* `sumIcc_norm_le_add_sub` / `sumIcc_norm_ge_sub`: comparing the `ℓ¹`-norms
  `‖∑_{n ≤ M} f n‖` and `‖∑_{n ≤ N} f n‖` of truncated sums of vectors of norm at most one;
* `afeMt_le_afeNt`, `afeNt_le_afeMt_add_two`: the two balanced truncation lengths
  `afeNt t = ⌊√(t/2π)⌋₊+1` and `afeMt t = ⌊t/(2π·afeNt t)⌋₊` differ by at most `2`;
* `cpow_cls_sub_one_eq_conj`: on the critical line `s = 1/2+it`, the dual summand
  `m^{s-1}` is the complex conjugate of the main summand `m^{-s}`.
-/

/-- **Truncated sums differ by at most the number of extra terms** (hard direction).
For `M ≤ N` and `‖f n‖ ≤ 1` for `n ≥ 1`,
`‖∑_{m ≤ M} f m‖ ≤ ‖∑_{n ≤ N} f n‖ + (N − M)`.

The point is that passing from `N` to `N − 1` can decrease the norm of the partial sum by at
most `1` (reverse triangle inequality). -/
lemma sumIcc_norm_le_add_sub {f : ℕ → ℂ} (hf : ∀ n, 1 ≤ n → ‖f n‖ ≤ 1) :
    ∀ {M N : ℕ}, M ≤ N →
      ‖∑ m ∈ Finset.Icc 1 M, f m‖ ≤ ‖∑ n ∈ Finset.Icc 1 N, f n‖ + ((N : ℝ) - M) := by
  intro M N
  induction N generalizing M with
  | zero =>
      intro h
      have hM : M = 0 := Nat.le_zero.mp h
      subst hM
      simp
  | succ N ih =>
      intro h
      rcases eq_or_lt_of_le h with heq | hlt
      · subst heq
        simp
      · have hMN : M ≤ N := Nat.lt_succ_iff.mp hlt
        have ih' := ih hMN
        have hsplit : ∑ n ∈ Finset.Icc 1 (N + 1), f n
            = ∑ n ∈ Finset.Icc 1 N, f n + f (N + 1) :=
          Finset.sum_Icc_succ_top (by omega) f
        have hfN : ‖f (N + 1)‖ ≤ 1 := hf (N + 1) (by omega)
        have hA : ‖∑ n ∈ Finset.Icc 1 N, f n‖
            ≤ ‖∑ n ∈ Finset.Icc 1 (N + 1), f n‖ + 1 := by
          have hsub := norm_sub_le ((∑ n ∈ Finset.Icc 1 N, f n) + f (N + 1)) (f (N + 1))
          rw [add_sub_cancel_right] at hsub
          rw [hsplit]
          linarith
        push_cast
        linarith [ih', hA, norm_nonneg (∑ n ∈ Finset.Icc 1 (N + 1), f n)]

/-- **Truncated sums differ by at most the number of extra terms** (easy direction).
For `M ≤ N` and `‖f n‖ ≤ 1` for `n ≥ 1`,
`‖∑_{n ≤ N} f n‖ ≤ ‖∑_{m ≤ M} f m‖ + (N − M)`,
by splitting off the extra terms and applying the triangle inequality. -/
lemma sumIcc_norm_ge_sub {f : ℕ → ℂ} (hf : ∀ n, 1 ≤ n → ‖f n‖ ≤ 1) :
    ∀ {M N : ℕ}, M ≤ N →
      ‖∑ n ∈ Finset.Icc 1 N, f n‖ ≤ ‖∑ m ∈ Finset.Icc 1 M, f m‖ + ((N : ℝ) - M) := by
  intro M N
  induction N generalizing M with
  | zero =>
      intro h
      have hM : M = 0 := Nat.le_zero.mp h
      subst hM
      simp
  | succ N ih =>
      intro h
      rcases eq_or_lt_of_le h with heq | hlt
      · subst heq
        simp
      · have hMN : M ≤ N := Nat.lt_succ_iff.mp hlt
        have ih' := ih hMN
        have hsplit : ∑ n ∈ Finset.Icc 1 (N + 1), f n
            = ∑ n ∈ Finset.Icc 1 N, f n + f (N + 1) :=
          Finset.sum_Icc_succ_top (by omega) f
        have hfN : ‖f (N + 1)‖ ≤ 1 := hf (N + 1) (by omega)
        push_cast
        calc ‖∑ n ∈ Finset.Icc 1 (N + 1), f n‖
            = ‖∑ n ∈ Finset.Icc 1 N, f n + f (N + 1)‖ := by rw [hsplit]
          _ ≤ ‖∑ n ∈ Finset.Icc 1 N, f n‖ + ‖f (N + 1)‖ := norm_add_le _ _
          _ ≤ (‖∑ m ∈ Finset.Icc 1 M, f m‖ + ((N : ℝ) - M)) + 1 := by linarith
          _ = ‖∑ m ∈ Finset.Icc 1 M, f m‖ + ((N : ℝ) + 1 - M) := by ring

/-- Comparing two truncated sums whose lengths differ by at most `2`. -/
lemma sumIcc_norm_le_of_le_add_two {f : ℕ → ℂ} (hf : ∀ n, 1 ≤ n → ‖f n‖ ≤ 1)
    {M N : ℕ} (hMN : M ≤ N + 2) (hNM : N ≤ M + 2) :
    ‖∑ m ∈ Finset.Icc 1 M, f m‖ ≤ ‖∑ n ∈ Finset.Icc 1 N, f n‖ + 2 := by
  have hNM' : ((N : ℝ) - M) ≤ 2 := by
    have h : ((N : ℝ)) ≤ (M : ℝ) + 2 := by exact_mod_cast hNM
    linarith
  have hMN' : ((M : ℝ) - N) ≤ 2 := by
    have h : ((M : ℝ)) ≤ (N : ℝ) + 2 := by exact_mod_cast hMN
    linarith
  rcases le_total M N with h | h
  · linarith [sumIcc_norm_le_add_sub hf h, norm_nonneg (∑ n ∈ Finset.Icc 1 N, f n)]
  · linarith [sumIcc_norm_ge_sub hf h, norm_nonneg (∑ m ∈ Finset.Icc 1 M, f m)]

/-! ## The two balanced truncation lengths differ by at most two -/

/-- `afeMt t ≤ afeNt t`: the dual cutoff never exceeds the main cutoff. -/
lemma afeMt_le_afeNt (t : ℝ) (ht : 1 ≤ t) : afeMt t ≤ afeNt t := by
  set x : ℝ := Real.sqrt (t / (2 * Real.pi)) with hx
  have hx2 : x ^ 2 = t / (2 * Real.pi) := by
    rw [hx]; exact Real.sq_sqrt (by positivity)
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have ht' : t = x ^ 2 * (2 * Real.pi) := by
    rw [hx2]; field_simp
  have hNpos : (0 : ℝ) < (afeNt t : ℝ) := by
    have h : (1 : ℕ) ≤ afeNt t := one_le_afeNt t
    exact_mod_cast h
  have hNgt : x < (afeNt t : ℝ) := by
    rw [afeNt, ← hx]; push_cast; exact Nat.lt_floor_add_one x
  rw [afeMt]
  refine le_of_lt ?_
  refine (Nat.floor_lt (by positivity : (0 : ℝ) ≤ t / (2 * Real.pi * (afeNt t : ℝ)))).mpr ?_
  refine (div_lt_iff₀ (by nlinarith [Real.pi_pos, hNpos] :
      (0 : ℝ) < 2 * Real.pi * (afeNt t : ℝ))).mpr ?_
  nlinarith [ht', hNgt, hx0, Real.pi_pos,
    mul_pos (sub_pos.mpr hNgt) (by linarith : (0 : ℝ) < x + (afeNt t : ℝ))]

/-- `afeNt t ≤ afeMt t + 2`: the main cutoff exceeds the dual cutoff by at most two. -/
lemma afeNt_le_afeMt_add_two (t : ℝ) (ht : 1 ≤ t) : afeNt t ≤ afeMt t + 2 := by
  set x : ℝ := Real.sqrt (t / (2 * Real.pi)) with hx
  have hx2 : x ^ 2 = t / (2 * Real.pi) := by
    rw [hx]; exact Real.sq_sqrt (by positivity)
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have ht' : t = x ^ 2 * (2 * Real.pi) := by
    rw [hx2]; field_simp
  have hNpos : (0 : ℝ) < (afeNt t : ℝ) := by
    have h : (1 : ℕ) ≤ afeNt t := one_le_afeNt t
    exact_mod_cast h
  have hNle : (afeNt t : ℝ) ≤ x + 1 := by
    rw [afeNt, ← hx]; push_cast
    linarith [Nat.floor_le hx0]
  rcases lt_or_ge x 1 with hx1 | hx1
  · -- `x < 1`, so `afeNt t = 1` and the claim is trivial
    have hF0 : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr hx1
    have hN1 : afeNt t = 1 := by rw [afeNt, ← hx, hF0]
    rw [hN1]; omega
  · -- `1 ≤ x`: `t/(2π·N) > x − 1`, hence `afeMt t > x − 2` and `⌊x⌋₊ < afeMt t + 2`
    have hyx : x - 1 < t / (2 * Real.pi * (afeNt t : ℝ)) := by
      refine (lt_div_iff₀ (by nlinarith [Real.pi_pos, hNpos] :
          (0 : ℝ) < 2 * Real.pi * (afeNt t : ℝ))).mpr ?_
      have h1 : (afeNt t : ℝ) * (x - 1) ≤ (x + 1) * (x - 1) :=
        mul_le_mul_of_nonneg_right hNle (by linarith)
      nlinarith [h1, ht', Real.pi_pos]
    have hMgt : x - 2 < (afeMt t : ℝ) := by
      have hfl : t / (2 * Real.pi * (afeNt t : ℝ)) < (afeMt t : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      linarith
    have hxlt : x < (afeMt t : ℝ) + 2 := by linarith
    have hFlt : ⌊x⌋₊ < afeMt t + 2 :=
      (Nat.floor_lt hx0).mpr (by push_cast; linarith)
    rw [afeNt, ← hx]
    omega

/-! ## The dual summand is the conjugate of the main summand -/

/-- On the critical line, `m^{s-1} = conj (m^{-s})` for every `m ≥ 1`. -/
lemma cpow_cls_sub_one_eq_conj (t : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    (m : ℂ) ^ (cls t - 1) = star ((m : ℂ) ^ (-(cls t))) := by
  have hstar : cls t - 1 = star (-(cls t)) := by
    simp only [cls]
    simp
    ring
  rw [hstar]
  have harg : (m : ℂ).arg ≠ Real.pi := by
    have h1 : (m : ℂ).arg = 0 := by
      rw [← Complex.ofReal_natCast]
      exact Complex.arg_ofReal_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ))
    rw [h1]; exact Real.pi_ne_zero.symm
  have hconj : star ((m : ℂ)) = (m : ℂ) := by
    rw [← Complex.ofReal_natCast]
    exact Complex.conj_ofReal (m : ℝ)
  have h := Complex.cpow_conj (m : ℂ) (-(cls t)) harg
  simp only [starRingEnd_apply, hconj] at h
  exact h

/-- The dual truncated sum is the conjugate of the main truncated sum at the *dual* cutoff. -/
lemma afeDual_eq_conj_sum (t : ℝ) :
    afeDual t = star (∑ m ∈ Finset.Icc 1 (afeMt t), (m : ℂ) ^ (-(cls t))) := by
  rw [afeDual_apply]
  have hms : star (∑ m ∈ Finset.Icc 1 (afeMt t), (m : ℂ) ^ (-(cls t)))
      = ∑ m ∈ Finset.Icc 1 (afeMt t), star ((m : ℂ) ^ (-(cls t))) :=
    map_sum (starRingEnd ℂ) _ _
  rw [hms]
  exact Finset.sum_congr rfl
    (fun m hm => cpow_cls_sub_one_eq_conj t (Finset.mem_Icc.mp hm).1)

/-- The dual sum is controlled by the main sum:
`‖Σ_{m ≤ afeMt t} m^{s-1}‖ ≤ ‖Σ_{n ≤ afeNt t} n^{-s}‖ + 3`. -/
lemma norm_afeDual_le_afeMain_add (t : ℝ) (ht : 1 ≤ t) :
    ‖afeDual t‖ ≤ ‖afeMain t‖ + 3 := by
  have hconj : afeDual t = star (∑ m ∈ Finset.Icc 1 (afeMt t), (m : ℂ) ^ (-(cls t))) :=
    afeDual_eq_conj_sum t
  have hnorm : ‖star (∑ m ∈ Finset.Icc 1 (afeMt t), (m : ℂ) ^ (-(cls t)))‖
      = ‖∑ m ∈ Finset.Icc 1 (afeMt t), (m : ℂ) ^ (-(cls t))‖ := Complex.norm_conj _
  rw [hconj, hnorm]
  have hcmp : ‖∑ m ∈ Finset.Icc 1 (afeMt t), (m : ℂ) ^ (-(cls t))‖
      ≤ ‖∑ n ∈ Finset.Icc 1 (afeNt t), (n : ℂ) ^ (-(cls t))‖ + 2 := by
    refine sumIcc_norm_le_of_le_add_two (fun n hn => norm_cpow_neg_cls_le_one hn) ?_ ?_
    · have h := afeMt_le_afeNt t ht
      omega
    · exact afeNt_le_afeMt_add_two t ht
  have hmain : ‖afeMain t‖ = ‖∑ n ∈ Finset.Icc 1 (afeNt t), (n : ℂ) ^ (-(cls t))‖ := by
    rw [afeMain_apply]
  rw [hmain]
  linarith

/-- **The sharp approximate functional equation for `ζ` on the critical line** (Titchmarsh,
*The Theory of the Riemann Zeta-Function*, Thm 4.11): there is an absolute `C > 0` with
`‖ζ(1/2+it)‖ ≤ C (1 + ‖Σ_{n ≤ ⌊√(t/2π)⌋₊+1} n^{-(1/2+it)}‖)` for every `t ≥ 1`.

This is the final assembly.  `Work.ZeroDensity.Ingham.AfeProof.zetaAfeResidual` (PROVED, axiom
clean) gives the balanced residual
`‖ζ(s) − Σ_{n ≤ afeNt t} n^{−s} − χ(s)·Σ_{m ≤ afeMt t} m^{s−1}‖ ≤ C₀`, `s = 1/2+it`,
with `afeNt t = ⌊√(t/2π)⌋₊+1` (the truncation of the statement) and
`afeMt t = ⌊t/(2π·afeNt t)⌋₊`.  Two elementary facts finish it:
* `‖χ(1/2+it)‖ = 1` (`Ingham.norm_zetaChi_critical`), so
  `‖ζ(s)‖ ≤ ‖Σ_{n≤afeNt t} n^{-s}‖ + ‖Σ_{m≤afeMt t} m^{s-1}‖ + C₀`;
* `Σ_{m≤afeMt t} m^{s-1}` is the conjugate of `Σ_{m≤afeMt t} m^{-(1/2+it)}` (termwise:
  `m^{s-1} = conj(m^{-(1/2+it)})` for `m ≥ 1`, since `log m` is real), hence has the same norm as
  `Σ_{m≤afeMt t} (m:ℂ)^{-(1/2+it)}`; and the two truncation lengths differ by at most `2`
  (`x := √(t/2π)`, `x ≤ afeNt t ≤ x+1`, `x − 1 ≤ t/(2π·afeNt t) ≤ x`, so
  `|afeMt t − afeNt t| ≤ 2`), each summand having modulus `m^{-1/2} ≤ 1`, so
  `‖Σ_{m≤afeMt t}(m)^{-(1/2+it)}‖ ≤ ‖Σ_{n≤afeNt t}(n)^{-(1/2+it)}‖ + 3`. -/
theorem zetaAfeSharp : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
    ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      C * (1 + ‖∑ n ∈ Finset.Icc 1 (⌊Real.sqrt (t / (2 * Real.pi))⌋₊ + 1),
        (n : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * Complex.I))‖) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := zetaAfeResidual
  refine ⟨C₀ + 3, by linarith, ?_⟩
  intro t ht
  have hres : ‖riemannZeta (cls t) - afeMain t - zetaChi (cls t) * afeDual t‖ ≤ C₀ := hC₀ t ht
  have hmain : (∑ n ∈ Finset.Icc 1 (⌊Real.sqrt (t / (2 * Real.pi))⌋₊ + 1),
        (n : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * Complex.I))) = afeMain t := rfl
  rw [hmain]
  have hchi : ‖zetaChi (cls t)‖ = 1 := norm_zetaChi_critical t
  have hdual : ‖afeDual t‖ ≤ ‖afeMain t‖ + 3 := norm_afeDual_le_afeMain_add t ht
  have hnormchi : ‖zetaChi (cls t) * afeDual t‖ = ‖afeDual t‖ := by
    rw [norm_mul, hchi, one_mul]
  calc ‖riemannZeta (cls t)‖
      = ‖(riemannZeta (cls t) - afeMain t - zetaChi (cls t) * afeDual t)
          + afeMain t + zetaChi (cls t) * afeDual t‖ := by
        congr 1; ring
    _ ≤ ‖(riemannZeta (cls t) - afeMain t - zetaChi (cls t) * afeDual t) + afeMain t‖
          + ‖zetaChi (cls t) * afeDual t‖ := norm_add_le _ _
    _ ≤ (‖riemannZeta (cls t) - afeMain t - zetaChi (cls t) * afeDual t‖ + ‖afeMain t‖)
          + ‖afeDual t‖ := by
        have h := norm_add_le (riemannZeta (cls t) - afeMain t - zetaChi (cls t) * afeDual t)
          (afeMain t)
        rw [hnormchi]
        linarith
    _ ≤ (C₀ + ‖afeMain t‖) + (‖afeMain t‖ + 3) := by linarith
    _ ≤ (C₀ + 3) * (1 + ‖afeMain t‖) := by
        nlinarith [norm_nonneg (afeMain t), hC₀pos]

end Work.ZeroDensity.Ingham.AfeProof
