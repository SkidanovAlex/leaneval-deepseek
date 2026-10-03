/-
# Half-lattice sums of `jbDecay` at exponent `11`

The sliding-window weight `ρ` of `boxDecomp` is bounded pointwise by
`(C₀ / M ^ 2) * (⟨r/M⟩^{-12} + (2 ^ 60 M / L) ⟨r/M⟩^{-11})`: the `ℓ¹`-loss of the class sums costs
exactly one power of the Japanese bracket, so the `ℤ`-lattice of `⟨·⟩^{-11}` has to be compared
with the integral.  This module supplies the two facts that are needed:

* `jbDecay_nat_shift_summable_gen` — the half-lattice of `jbDecay N` is summable for every
  `N ≥ 2` (the threshold `12` in `jbDecay_nat_shift_summable` is an artefact of `riemann_shift`);
* `jbDecay_nat_shift_lattice_le11` and `jbDecay_int_lattice_le11` — the Riemann comparison at
  `⟨t⟩^{-11}`, i.e. `∑_{k} ⟨t + k λ⟩^{-12} ≤ 2 ^ 60 λ^{-1} ⟨t⟩^{-11}` and its `ℤ`-lattice
  counterpart `∑_{r} ⟨r/M⟩^{-11} ≤ 2 * (2 ^ 60 M)`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.winBase

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-- **Summability of `⟨t + ℕ lam⟩^{-N}` for every `N ≥ 2`.**  The threshold `12` of
`jbDecay_nat_shift_summable` is an artefact of the Riemann comparison `riemann_shift`, not of the
summability. -/
theorem jbDecay_nat_shift_summable_gen {N : ℕ} (hN : 2 ≤ N) {lam : ℝ} (h0 : 0 < lam) {t : ℝ}
    (ht : 0 ≤ t) : Summable fun k : ℕ => jbDecay N (t + (k : ℝ) * lam) := by
  obtain ⟨K, hK, hK1⟩ : ∃ K : ℕ, 2 * t ≤ (K : ℝ) * lam ∧ 1 ≤ K := by
    refine ⟨⌈2 * t / lam⌉₊ + 1, ?_, by omega⟩
    have h1 : 2 * t / lam ≤ (((⌈2 * t / lam⌉₊ : ℕ) : ℝ)) := Nat.le_ceil _
    have h2 : (((⌈2 * t / lam⌉₊ : ℕ) : ℝ)) ≤ (((⌈2 * t / lam⌉₊ + 1 : ℕ) : ℝ)) := by
      push_cast; linarith
    have h3 := mul_le_mul_of_nonneg_right (h1.trans h2) h0.le
    rwa [div_mul_cancel₀ _ h0.ne'] at h3
  rw [← summable_nat_add_iff K]
  have hbase : Summable fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1) ^ N := by
    have h := (Real.summable_one_div_nat_pow (p := N)).mpr (by omega)
    have h2 := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ N) 1).mpr h
    refine h2.congr (fun k => ?_)
    push_cast
    ring_nf
  refine Summable.of_nonneg_of_le (fun k => jbDecay_nonneg N _) (fun k => ?_)
    (hbase.mul_left ((lam ^ N)⁻¹))
  have hKc : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
  have hx : ((k : ℝ) + 1) * lam ≤ t + (((k + K : ℕ) : ℝ)) * lam := by
    have hcast : (((k + K : ℕ) : ℝ)) = (k : ℝ) + K := by push_cast; ring
    rw [hcast]
    have hKK : (k : ℝ) + 1 ≤ (k : ℝ) + K := by linarith
    have := mul_le_mul_of_nonneg_right hKK h0.le
    nlinarith [hK]
  have hxpos : 0 < ((k : ℝ) + 1) * lam := by positivity
  have hjb : ((k : ℝ) + 1) * lam ≤ jb (t + (((k + K : ℕ) : ℝ)) * lam) :=
    hx.trans ((le_abs_self _).trans (abs_le_jb _))
  calc jbDecay N (t + (((k + K : ℕ) : ℝ)) * lam)
      = (jb (t + (((k + K : ℕ) : ℝ)) * lam))⁻¹ ^ N := rfl
    _ ≤ (((k : ℝ) + 1) * lam)⁻¹ ^ N :=
        pow_le_pow_left₀ (jb_inv_nonneg _) (inv_le_inv₀ (jb_pos _) hxpos |>.mpr hjb) N
    _ = (lam ^ N)⁻¹ * (1 / ((k : ℝ) + 1) ^ N) := by
        rw [mul_inv, mul_pow, inv_pow, div_eq_mul_inv]
        ring

/-- **The half-lattice Riemann comparison at `⟨t⟩^{-11}`.**  A lattice sum of `⟨·⟩^{-12}` costs
the counting factor `2 ^ 60 / lam` and loses exactly one power of the bracket. -/
theorem jbDecay_nat_shift_lattice_le11 {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) {t : ℝ}
    (ht : 0 ≤ t) :
    (∑' k : ℕ, jbDecay 11 (t + (k : ℝ) * lam)) ≤ (2 : ℝ) ^ 60 * lam⁻¹ := by
  have h := riemann_shift 10 (by norm_num) (ε := lam) (t := t) h0 h1 ht
  have hX : (∑' k : ℕ, lam * jbDecay 11 (t + lam * (k : ℝ)))
      = lam * ∑' k : ℕ, jbDecay 11 (t + (k : ℝ) * lam) := by
    rw [tsum_mul_left]
    congr 1
    exact tsum_congr (fun k => by ring_nf)
  rw [hX] at h
  have hb : (2 : ℝ) ^ 60 * jbDecay 10 t ≤ (2 : ℝ) ^ 60 := by
    nlinarith [jbDecay_le_one 10 t, pow_pos (by norm_num : (0:ℝ) < 2) 60]
  rw [show (2 : ℝ) ^ 60 * lam⁻¹ = (2 : ℝ) ^ 60 / lam from (div_eq_mul_inv _ _).symm,
    le_div_iff₀ h0]
  linarith [h.trans hb]

/-- **The full `ℤ`-lattice comparison at `⟨·⟩^{-11}`.** -/
theorem jbDecay_int_lattice_le11 {M : ℝ} (hM : 1 ≤ M) :
    (∑' r : ℤ, jbDecay 11 ((r : ℝ) / M)) ≤ 2 * ((2 : ℝ) ^ 60 * M) := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hlam0 : 0 < M⁻¹ := inv_pos.mpr hMpos
  have hlam1 : M⁻¹ ≤ 1 := by rw [inv_le_one₀ hMpos]; exact hM
  set F : ℤ → ℝ := fun r => jbDecay 11 ((r : ℝ) / M) with hF
  have hFpos : Summable fun k : ℕ => F (k : ℤ) := by
    have h := jbDecay_nat_shift_summable_gen (N := 11) (by norm_num) (lam := M⁻¹) hlam0
      (t := 0) le_rfl
    refine h.congr (fun k => ?_)
    simp only [hF]
    congr 1
    rw [div_eq_mul_inv]
    push_cast
    ring
  have hFneg : Summable fun k : ℕ => F (-(k + 1 : ℤ)) := by
    have h := jbDecay_nat_shift_summable_gen (N := 11) (by norm_num) (lam := M⁻¹) hlam0
      (t := M⁻¹) (by positivity)
    refine h.congr (fun k => ?_)
    simp only [hF]
    conv_lhs => rw [← jbDecay_neg]
    exact congrArg (jbDecay 11) (by push_cast; rw [div_eq_mul_inv]; ring)
  have hsplit : (∑' r : ℤ, F r) = (∑' k : ℕ, F (k : ℤ)) + (∑' k : ℕ, F (-(k + 1 : ℤ))) :=
    tsum_of_nat_of_neg_add_one (f := F) hFpos hFneg
  have h1 : (∑' k : ℕ, F (k : ℤ)) ≤ (2 : ℝ) ^ 60 * (M⁻¹)⁻¹ := by
    have h := jbDecay_nat_shift_lattice_le11 (lam := M⁻¹) hlam0 hlam1 (t := 0) le_rfl
    have h' : (∑' k : ℕ, jbDecay 11 (0 + (k : ℝ) * M⁻¹)) = (∑' k : ℕ, F (k : ℤ)) :=
      tsum_congr (fun k => by
        simp only [hF]
        congr 1
        rw [div_eq_mul_inv]
        push_cast
        ring)
    rwa [h'] at h
  have h2 : (∑' k : ℕ, F (-(k + 1 : ℤ))) ≤ (2 : ℝ) ^ 60 * (M⁻¹)⁻¹ := by
    have h := jbDecay_nat_shift_lattice_le11 (lam := M⁻¹) hlam0 hlam1 (t := M⁻¹) (by positivity)
    have h' : (∑' k : ℕ, jbDecay 11 (M⁻¹ + (k : ℝ) * M⁻¹)) = (∑' k : ℕ, F (-(k + 1 : ℤ))) :=
      tsum_congr (fun k => by
        simp only [hF]
        conv_lhs => rw [← jbDecay_neg]
        exact congrArg (jbDecay 11) (by push_cast; rw [div_eq_mul_inv]; ring))
    rwa [h'] at h
  rw [hsplit]
  rw [inv_inv] at h1 h2
  linarith

/-- **The half-lattice Riemann comparison, general exponent.**  For `n ≥ 1`,
`∑_k ⟨t + k λ⟩^{-(n+1)} ≤ 2 ^ 60 λ^{-1} ⟨t⟩^{-n}`: the lattice sum costs the counting factor
`2 ^ 60 / λ` and loses exactly one power of the Japanese bracket. -/
theorem jbDecay_nat_shift_lattice_le_gen {n : ℕ} (hn : 1 ≤ n) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    (∑' k : ℕ, jbDecay (n + 1) (t + (k : ℝ) * lam)) ≤ (2 : ℝ) ^ 60 * lam⁻¹ * jbDecay n t := by
  have h := riemann_shift n hn (ε := lam) (t := t) h0 h1 ht
  have hX : (∑' k : ℕ, lam * jbDecay (n + 1) (t + lam * (k : ℝ)))
      = lam * ∑' k : ℕ, jbDecay (n + 1) (t + (k : ℝ) * lam) := by
    rw [tsum_mul_left]
    congr 1
    exact tsum_congr (fun k => by ring)
  rw [hX] at h
  rw [show (2 : ℝ) ^ 60 * lam⁻¹ * jbDecay n t = ((2 : ℝ) ^ 60 * jbDecay n t) / lam from by
    rw [div_eq_mul_inv]; ring, le_div_iff₀ h0, mul_comm]
  exact h

/-- Summability of `⟨k/M⟩^{-11}` along `ℕ`. -/
theorem summable_jbDecay_eleven_nat_div {M : ℝ} (hM : 0 < M) :
    Summable fun k : ℕ => jbDecay 11 (((k : ℤ) : ℝ) / M) := by
  have hlam0 : 0 < M⁻¹ := inv_pos.mpr hM
  have h := jbDecay_nat_shift_summable_gen (N := 11) (by norm_num) (lam := M⁻¹) hlam0
    (t := 0) le_rfl
  refine h.congr (fun k => ?_)
  congr 1
  rw [div_eq_mul_inv]
  push_cast
  ring

/-- Summability of `⟨-(k+1)/M⟩^{-11}` along `ℕ`. -/
theorem summable_jbDecay_eleven_nat_neg_div {M : ℝ} (hM : 0 < M) :
    Summable fun k : ℕ => jbDecay 11 (((-(k + 1 : ℤ)) : ℝ) / M) := by
  have hlam0 : 0 < M⁻¹ := inv_pos.mpr hM
  have h := jbDecay_nat_shift_summable_gen (N := 11) (by norm_num) (lam := M⁻¹) hlam0
    (t := M⁻¹) (by positivity)
  refine h.congr (fun k => ?_)
  conv_lhs => rw [← jbDecay_neg]
  exact congrArg (jbDecay 11) (by push_cast; rw [div_eq_mul_inv]; ring)

/-- **Summability of the `ℤ`-lattice of `⟨·⟩^{-11}`.** -/
theorem summable_jbDecay_eleven_int_div {M : ℝ} (hM : 0 < M) :
    Summable fun r : ℤ => jbDecay 11 ((r : ℝ) / M) := by
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · simpa using summable_jbDecay_eleven_nat_div hM
  · simpa using summable_jbDecay_eleven_nat_neg_div hM


end Work.KMTAreas.A4
