/-
# The window conditions of the small-scale low case, strict form

`Work.KMTPlan.A6.lowSmallWindowConds` proves that on the admissible index set
`I^{max(l₁,l₂),k₁,k₂}` and for `L = lcL l₁ l₂ k₁ k₂` large enough, the two window conditions of
the small-scale low case hold:

* `max k₁ k₂ + 2 u ≤ Log N` with `u = uScale ρ L` (the window contains the bumps);
* `L ≤ 2 u` (the window is finer than the spacing of the arithmetic frequencies).

The first of these is used downstream (`lowSmallScaled`) in the **strict** form

  `max k₁ k₂ + 2 u + 1 ≤ Log N`,

which is what makes the narrow window `η_{≤-2u}` sit *strictly* inside the band, i.e. it is the
form in which the functional calculus of §6/§7 applies (the bump `φ_{N,t}` is supported below the
cut, with a strict inequality; see the hypothesis list of
`Work.KMTPlan.A6.lowSmallScaled_of_approx`).  This module proves that strict form.

## The mathematics

The argument is the same as in `lowSmallWindowConds`, but the pure arithmetic input is
strengthened: with `R = Log N`, `q = LogLog N` (so `2^q ≤ R + 2`) and `L ≤ C₀ q`, `2ρC₀ ≤ 1/8`,
one has `max k₁ k₂ ≤ L ≤ q^2` (because `q ≥ max C₀ 8`) and `uScale ρ L ≤ 2^{q/2}`, and then

  `max k₁ k₂ + 2u ≤ q^2 + 2^{q/2+1} ≤ 2^{q-2} + 2^{q-2} = 2^{q-1} ≤ 2^q - 3`,

using `q^2 ≤ 2^{q-2}` and `2^{q/2+1} ≤ 2^{q-2}` for `q ≥ 8` (`mainRegimeArithStrict` below, a
strict strengthening of `Work.KMTPlan.A6.mainRegimeArith`, whose conclusion is
`k + 2y ≤ 2^q - 2`).  Since `2^q - 2 ≤ R` (from `2^q ≤ R + 2`) this gives
`max k₁ k₂ + 2u + 1 ≤ R`, as required.

The threshold `B₀` is the maximum of the one from `lowSmallWindowConds` (which supplies the
second conjunct) and `C₀ · max C₀ 8` (which supplies `q ≥ max C₀ 8`).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.lowSmallWindowConds

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open Work.Analysis.EndVar

/-! ## Two elementary estimates -/

/-- Quadratic beats exponential with a factor `4` to spare: `q^2 ≤ 2^{q-2}` for `q ≥ 8`
(equality at `q = 8`, then the induction step uses `(q+1)^2 ≤ 2q^2` for `q ≥ 3`). -/
private lemma sq_le_two_pow_sub_two (q : ℕ) (hq : 8 ≤ q) : q ^ 2 ≤ 2 ^ (q - 2) := by
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ q hq ih =>
    rw [show q + 1 - 2 = q - 1 from by omega]
    have hstep : (q + 1) ^ 2 ≤ 2 * q ^ 2 := by nlinarith
    calc (q + 1) ^ 2 ≤ 2 * q ^ 2 := hstep
      _ ≤ 2 * 2 ^ (q - 2) := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (q - 1) := by
            rw [show q - 1 = (q - 2) + 1 from by omega, pow_succ]
            ring

/-- **Strengthened `mainRegimeArith`.**  In the main regime `q ≥ 8`, `k ≤ C₀ q` with `C₀ ≤ q`,
and `y ≤ 2^{q/2}`, one has `k + 2y ≤ 2^q - 3` (the version in `mainRegimeArith` gives only
`≤ 2^q - 2`).  The extra room comes from `k ≤ q^2 ≤ 2^{q-2} = 2^q/4`. -/
private lemma mainRegimeArithStrict (C₀ q k : ℕ) (y : ℝ) (hCq : C₀ ≤ q)
    (hq : 8 ≤ q) (hk : k ≤ C₀ * q) (hy : y ≤ (2 : ℝ) ^ ((q : ℝ) / 2)) :
    (k : ℝ) + 2 * y ≤ (2 : ℝ) ^ q - 3 := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hkq : k ≤ q * q := le_trans hk (Nat.mul_le_mul_right q hCq)
  have hkR : (k : ℝ) ≤ (q : ℝ) ^ 2 := by
    have h : (k : ℝ) ≤ ((q * q : ℕ) : ℝ) := by exact_mod_cast hkq
    push_cast at h
    linarith
  -- `q^2 ≤ 2^q / 4`
  have hquad : (q : ℝ) ^ 2 ≤ (2 : ℝ) ^ q / 4 := by
    have hnat : q ^ 2 ≤ 2 ^ (q - 2) := sq_le_two_pow_sub_two q hq
    have hcast : ((q ^ 2 : ℕ) : ℝ) ≤ ((2 ^ (q - 2) : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at hcast
    have h1 : q = (q - 2) + 2 := by omega
    have hsplit : (2 : ℝ) ^ q = 4 * (2 : ℝ) ^ (q - 2) := by
      conv_lhs => rw [h1, pow_add]
      ring
    rw [hsplit]
    linarith
  -- `2y ≤ 2^q / 4`
  have hy2 : 2 * y ≤ (2 : ℝ) ^ q / 4 := by
    have hq3 : (q : ℝ) / 2 ≤ (q : ℝ) - 3 := by
      have : (8 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      linarith
    have hsub : (2 : ℝ) ^ ((q : ℝ) - 3) = (2 : ℝ) ^ q / 8 := by
      rw [Real.rpow_sub h2pos, Real.rpow_natCast]
      norm_num
    have hmono : (2 : ℝ) ^ ((q : ℝ) / 2) ≤ (2 : ℝ) ^ q / 8 := by
      have hle := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hq3
      rw [hsub] at hle
      exact hle
    calc 2 * y ≤ 2 * (2 : ℝ) ^ ((q : ℝ) / 2) := mul_le_mul_of_nonneg_left hy (by norm_num)
      _ ≤ 2 * ((2 : ℝ) ^ q / 8) := by linarith
      _ = (2 : ℝ) ^ q / 4 := by ring
  have hx6 : (6 : ℝ) ≤ (2 : ℝ) ^ q := by
    have hle : (2 : ℝ) ^ 6 ≤ (2 : ℝ) ^ q := pow_le_pow_right₀ (by norm_num) (by omega)
    have h6 : (6 : ℝ) ≤ (2 : ℝ) ^ 6 := by norm_num
    linarith
  linarith

/-! ## The main theorem -/

theorem lowSmallWindowCondsStrict (ρ : ℝ) (hρ : 0 < ρ) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (hρC₀ : ρ * (C₀ : ℝ) ≤ 1 / 8) :
    ∃ B₀ : ℕ, ∀ (l₁ l₂ k₁ k₂ N : ℕ),
      Work.Analysis.EndVar.inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) N →
      B₀ ≤ Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ →
      (max k₁ k₂ + 2 * Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) + 1
          ≤ (Work.Analysis.EndVar.logN N).toNat) ∧
        Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂
          ≤ 2 * Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) := by
  obtain ⟨B₁, hB₁⟩ := lowSmallWindowConds ρ hρ C₀ hC₀ hρC₀
  refine ⟨max B₁ (C₀ * max C₀ 8), ?_⟩
  intro l₁ l₂ k₁ k₂ N hidx hB
  have hρC : ρ * (C₀ : ℝ) ≤ 1 / 4 := by linarith
  have hB₁L : B₁ ≤ lcL l₁ l₂ k₁ k₂ := le_trans (le_max_left _ _) hB
  have hBbig : C₀ * max C₀ 8 ≤ lcL l₁ l₂ k₁ k₂ := le_trans (le_max_right _ _) hB
  -- the second conjunct is exactly the (non-strict) `lowSmallWindowConds`
  obtain ⟨-, hsecond⟩ := hB₁ l₁ l₂ k₁ k₂ N hidx hB₁L
  refine ⟨?_, hsecond⟩
  set L : ℕ := lcL l₁ l₂ k₁ k₂ with hLdef
  obtain ⟨hl₁, hl₂, hk₁, hk₂⟩ :=
    (inIndexSet_iff_le (C₀ := C₀) (l₁ := l₁) (l₂ := l₂) (k₁ := k₁) (k₂ := k₂) (N := N)).mp hidx
  set n : ℕ := Nat.log 2 (max N 2) with hn
  set q : ℕ := Work.Analysis.EndVar.logLogN N with hqdef
  have hq : q = Nat.log 2 (n + 2) := by rw [hqdef, hn]; rfl
  have hheight : heightScale C₀ N = C₀ * q := by rw [heightScale, hqdef]
  have hLle : L ≤ C₀ * q := by
    have h : L ≤ heightScale C₀ N := by
      rw [hLdef, lcL]
      exact max_le (max_le hl₁ hl₂) (max_le hk₁ hk₂)
    rwa [hheight] at h
  have hQle : max C₀ 8 ≤ q :=
    Nat.le_of_mul_le_mul_left (le_trans hBbig hLle) (by omega)
  have hCq : C₀ ≤ q := le_trans (le_max_left _ _) hQle
  have hq8 : 8 ≤ q := le_trans (le_max_right _ _) hQle
  have hpow : 2 ^ q ≤ n + 2 := by
    rw [hq]; exact Nat.pow_log_le_self 2 (by omega)
  have hmL : max k₁ k₂ ≤ L := by rw [hLdef, lcL]; exact le_max_right _ _
  have hkq : max k₁ k₂ ≤ C₀ * q := le_trans hmL hLle
  have hy : (Work.KMTAreas.A7.uScale ρ L : ℝ) ≤ (2 : ℝ) ^ ((q : ℝ) / 2) :=
    uScaleHalfPow ρ hρ C₀ q L L hρC le_rfl hLle
  have h1 : max (k₁ : ℝ) (k₂ : ℝ) + 2 * (Work.KMTAreas.A7.uScale ρ L : ℝ)
      ≤ (2 : ℝ) ^ q - 3 := by
    have h := mainRegimeArithStrict C₀ q (max k₁ k₂) _ hCq hq8 hkq hy
    simpa only [Nat.cast_max] using h
  have h2 : (2 : ℝ) ^ q - 2 ≤ (n : ℝ) := by
    have h3 : ((2 ^ q : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast hpow
    push_cast at h3
    linarith
  have h4 : (((max k₁ k₂) + 2 * Work.KMTAreas.A7.uScale ρ L + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    push_cast
    linarith
  have h5 : max k₁ k₂ + 2 * Work.KMTAreas.A7.uScale ρ L + 1 ≤ n := by exact_mod_cast h4
  have hlog : (logN N).toNat = n := by simp only [logN, hn, Int.toNat_natCast]
  rw [hlog]
  exact h5

end Work.KMTPlan.A6
