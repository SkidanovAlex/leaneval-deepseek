import Mathlib
import Submission.Work.KMTAreas.A7.varphiNt_support_le
import Submission.Work.KMTPlan.A6.lowSmallWindowConds

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open Work.Analysis.EndVar

/-! ## The arithmetic input

Both estimates below are the elementary "exponential beats quadratic" facts needed to absorb the
two window terms `k` (linear in the height) and `uScale ρ L = ⌊2^{2ρL}⌋ ≤ 2^{q/2}` (where
`q = LogLog N`) into `Log N ≈ 2^q`.

The proof of `varphiNt_support_lowSmall` uses only `inIndexSet` (`L ≤ C₀ · LogLog N`, where
`L = lcL l₁ l₂ k₁ k₂ = max(max l₁ l₂)(max k₁ k₂)`) and the separation `ρC₀ ≤ 1/8` — the cut
`Nr ≤ splitCut ρ L` is not needed for this arithmetic step.  With the threshold
`B = C₀ · max C₀ 8` we get `max C₀ 8 ≤ q = LogLog N`, hence `C₀ ≤ q ≤ 8` and `q ≥ 8`; then

* `max k₁ k₂ ≤ L ≤ C₀ q ≤ q²`,
* `uScale ρ L = ⌊2^{2ρL}⌋ ≤ 2^{2ρC₀ q} ≤ 2^{q/4} ≤ 2^{q/2}`  (`uScaleHalfPow`),

and `q² + 3·2^{q/2} ≤ 2^{q-2} + 2^{q-2} = 2^{q-1} ≤ 2^q - 2 ≤ Log N`, since
`2^q ≤ Log N + 2` by `Nat.pow_log_le_self` applied to `q = log₂ (Log N + 2)`. -/

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

/-- In the main regime `q ≥ 8`, `k ≤ C₀ q` with `C₀ ≤ q` and `y ≤ 2^{q/2}`, one has
`k + 3y ≤ 2^q - 2`.  This is the strengthened version of `mainRegimeArith` needed for the
*three* window terms `k + 3u` of the small-scale low case: the room comes from
`k ≤ q^2 ≤ 2^{q-2}` and `3·2^{q/2} ≤ 2^{q-2}`. -/
private lemma mainRegimeArith3 (C₀ q k : ℕ) (y : ℝ) (hCq : C₀ ≤ q) (hq : 8 ≤ q)
    (hk : k ≤ C₀ * q) (hy : y ≤ (2 : ℝ) ^ ((q : ℝ) / 2)) :
    (k : ℝ) + 3 * y ≤ (2 : ℝ) ^ q - 2 := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  set x : ℝ := (2 : ℝ) ^ q with hxdef
  have hxnn : 0 ≤ x := by rw [hxdef]; positivity
  -- `k ≤ q^2`
  have hkq : k ≤ q * q := le_trans hk (Nat.mul_le_mul_right q hCq)
  have hkR : (k : ℝ) ≤ (q : ℝ) ^ 2 := by
    have h : (k : ℝ) ≤ ((q * q : ℕ) : ℝ) := by exact_mod_cast hkq
    push_cast at h
    linarith
  -- `q^2 ≤ 2^q / 4`
  have hquad : (q : ℝ) ^ 2 ≤ x / 4 := by
    have hnat : q ^ 2 ≤ 2 ^ (q - 2) := sq_le_two_pow_sub_two q hq
    have hcast : ((q ^ 2 : ℕ) : ℝ) ≤ ((2 ^ (q - 2) : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at hcast
    have hsplit : x = 4 * (2 : ℝ) ^ (q - 2) := by
      conv_lhs => rw [hxdef, show q = (q - 2) + 2 from by omega, pow_add]
      ring
    rw [hsplit]
    linarith
  -- `3y ≤ 2^q / 4`
  have hy4 : 3 * y ≤ x / 4 := by
    have hq4 : (q : ℝ) / 2 ≤ (q : ℝ) - 4 := by
      have : (8 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      linarith
    have hmono : (2 : ℝ) ^ ((q : ℝ) / 2) ≤ (2 : ℝ) ^ ((q : ℝ) - 4) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hq4
    have hsub : (2 : ℝ) ^ ((q : ℝ) - 4) = x / 16 := by
      rw [Real.rpow_sub h2pos, Real.rpow_natCast, hxdef]
      norm_num
    have hy16 : 3 * y ≤ 3 * ((2 : ℝ) ^ ((q : ℝ) / 2)) := by linarith
    have h316 : 3 * (x / 16) ≤ x / 4 := by linarith
    linarith
  have hx4 : (4 : ℝ) ≤ x := by
    rw [hxdef]
    calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (2 : ℝ) ^ q := pow_le_pow_right₀ (by norm_num) (by omega)
  linarith

/-- **The window condition `k + 3u ≤ Log N` on the small-scale set, for large `L`.**
This is the arithmetic input that makes the supports `2^{-3u}`, `2^{-3du}` of the two modulated
bumps available to `Work.KMTPlan.A6.ssuBtwistEx`; it is strictly stronger than
`Work.KMTPlan.A6.lowSmallWindowConds` (`max k + 2u ≤ Log N`), and follows from
`inIndexSet` (`L ≤ C₀ logLogN N`), `N ≤ splitCut ρ L` and `2ρC₀ ≤ 1/8` for `L ≥ B(ρ,C₀)`.
(For `B = 0` the claim is FALSE - e.g. `C₀ = 1`, `L = 2`, `N = 4`, `k₁ = 2` - which is why the
threshold `B` is part of the statement.) -/
theorem varphiNt_support_lowSmall (ρ : Real) (hρ : 0 < ρ) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (hρC₀ : ρ * (C₀ : Real) ≤ 1 / 8) :
    ∃ B : ℕ, ∀ (l₁ l₂ k₁ k₂ Nr : ℕ),
      Work.Analysis.EndVar.inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) Nr →
      Nr ≤ Work.KMTAreas.A7.splitCut ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) →
      B ≤ Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ →
      max k₁ k₂ + 3 * Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)
        ≤ (Work.Analysis.EndVar.logN Nr).toNat := by
  refine ⟨C₀ * max C₀ 8, ?_⟩
  intro l₁ l₂ k₁ k₂ Nr hidx _hsplit hB
  have hρC : ρ * (C₀ : ℝ) ≤ 1 / 4 := by linarith
  set L : ℕ := lcL l₁ l₂ k₁ k₂ with hLdef
  obtain ⟨hl₁, hl₂, hk₁, hk₂⟩ :=
    (inIndexSet_iff_le (C₀ := C₀) (l₁ := l₁) (l₂ := l₂) (k₁ := k₁) (k₂ := k₂)
      (N := Nr)).mp hidx
  set n : ℕ := Nat.log 2 (max Nr 2) with hn
  set q : ℕ := logLogN Nr with hqdef
  have hq : q = Nat.log 2 (n + 2) := by rw [hqdef, hn]; rfl
  have hheight : heightScale C₀ Nr = C₀ * q := by rw [heightScale, hqdef]
  -- the height scale bounds `L`
  have hLle : L ≤ C₀ * q := by
    have h : L ≤ heightScale C₀ Nr := by
      rw [hLdef, lcL]
      exact max_le (max_le hl₁ hl₂) (max_le hk₁ hk₂)
    rwa [hheight] at h
  -- hence `q ≥ max C₀ 8`
  have hQle : max C₀ 8 ≤ q :=
    Nat.le_of_mul_le_mul_left (le_trans hB hLle) (by omega)
  have hCq : C₀ ≤ q := le_trans (le_max_left _ _) hQle
  have hq8 : 8 ≤ q := le_trans (le_max_right _ _) hQle
  -- the two window terms
  have hmL : max k₁ k₂ ≤ L := by rw [hLdef, lcL]; exact le_max_right _ _
  have hkq : max k₁ k₂ ≤ C₀ * q := le_trans hmL hLle
  have hy : (Work.KMTAreas.A7.uScale ρ L : ℝ) ≤ (2 : ℝ) ^ ((q : ℝ) / 2) :=
    uScaleHalfPow ρ hρ C₀ q L L hρC le_rfl hLle
  have h1 : max (k₁ : ℝ) (k₂ : ℝ) + 3 * (Work.KMTAreas.A7.uScale ρ L : ℝ)
      ≤ (2 : ℝ) ^ q - 2 := by
    have h := mainRegimeArith3 C₀ q (max k₁ k₂) _ hCq hq8 hkq hy
    simpa only [Nat.cast_max] using h
  -- and `2^q ≤ Log N + 2`
  have hpow : 2 ^ q ≤ n + 2 := by
    rw [hq]; exact Nat.pow_log_le_self 2 (by omega)
  have h2 : (2 : ℝ) ^ q - 2 ≤ (n : ℝ) := by
    have h3 : ((2 ^ q : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast hpow
    push_cast at h3
    linarith
  have h4 : (((max k₁ k₂) + 3 * Work.KMTAreas.A7.uScale ρ L : ℕ) : ℝ) ≤ (n : ℝ) := by
    push_cast
    linarith
  have h5 : max k₁ k₂ + 3 * Work.KMTAreas.A7.uScale ρ L ≤ n := by exact_mod_cast h4
  have hlog : (logN Nr).toNat = n := by simp only [logN, hn, Int.toNat_natCast]
  rw [hlog]
  exact h5

end Work.KMTPlan.A6
