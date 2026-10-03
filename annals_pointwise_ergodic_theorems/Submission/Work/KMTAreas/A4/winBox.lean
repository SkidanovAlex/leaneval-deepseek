/-
# The sliding-window decomposition of a decaying sequence

`boxDecomp` is the analytic heart of the reduction of the smooth window `win M 0` to a *sharp*
interval sum (`Work.KMTAreas.A4.winSum_reduce`): a sequence `w` whose adjacent differences decay
like `C₀ / M ^ 2 * ⟨n/M⟩^{-12}`, whose values decay like `C₁ / M * ⟨n/M⟩^{-12}`, and whose sums
along every residue class mod `L` vanish, is an `ℓ¹`-combination of the interval indicators
`1_{[k,k+L-1]}` with total mass `O((C₀+C₁)/L)`.

The vanishing of the class sums is what makes the sliding weight
`ρ r = ∑'_{j:ℕ} (w (r - j L) - w (r - j L - 1))` decay: it turns the naive (divergent) half-line
sum into the *forward* form `ρ r = d r - ∑'_{j:ℕ} d (r + j L)` for `r ≥ 0`, and the reflected
half-line for `r < 0`.  Each half-line costs one power of the Japanese bracket
(`box_halfSum_pos`, `box_halfSum_neg`), and the resulting `ℤ`-lattice sums are compared with the
integral in `winB11`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.winB11
import Submission.Work.KMTAreas.A4.slideSum_eq

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-! ## The half-line sums along a residue class -/

/-- **The half-line sum along a residue class, positive direction.**  If `d` decays like
`C₀/M² ⟨n/M⟩^{-12}` then the sum of `‖d‖` along `r, r+L, r+2L, …` (`1 ≤ L ≤ M`, `r ≥ 0`) is
`C₀/M² · (2^60 M/L) ⟨r/M⟩^{-11}`: the lattice costs the counting factor `2^60 M/L` and gains
exactly one power of the Japanese bracket. -/
theorem box_halfSum_pos (L : ℕ) (M C₀ : ℝ) (hL : 1 ≤ L) (hM : 0 < M) (hLM : (L : ℝ) ≤ M)
    (hC₀ : 0 < C₀) (d : ℤ → ℂ)
    (hd : ∀ n : ℤ, ‖d n‖ ≤ C₀ / M ^ 2 * jbDecay 12 ((n : ℝ) / M)) (r : ℤ) (hr : 0 ≤ r) :
    (∑' j : ℕ, ‖d (r + (j : ℤ) * (L : ℤ))‖)
      ≤ C₀ / M ^ 2 * ((2 : ℝ) ^ 60 * M / (L : ℝ)) * jbDecay 11 ((r : ℝ) / M) := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hrpos : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  set lam : ℝ := (L : ℝ) / M with hlam
  set t : ℝ := (r : ℝ) / M with ht
  have hlam0 : 0 < lam := by rw [hlam]; exact div_pos hLpos hM
  have hlam1 : lam ≤ 1 := by rw [hlam, div_le_one hM]; exact hLM
  have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg hrpos hM.le
  have hC : (0 : ℝ) ≤ C₀ / M ^ 2 := by positivity
  have hsum := jbDecay_nat_shift_lattice_le_gen (n := 11) (by norm_num) hlam0 hlam1 ht0
  have harg : ∀ j : ℕ, (((r + (j : ℤ) * (L : ℤ) : ℤ)) : ℝ) / M = t + (j : ℝ) * lam := by
    intro j
    rw [ht, hlam]
    push_cast
    ring
  have hle : ∀ j : ℕ, ‖d (r + (j : ℤ) * (L : ℤ))‖
      ≤ C₀ / M ^ 2 * jbDecay 12 (t + (j : ℝ) * lam) := by
    intro j
    have h := hd (r + (j : ℤ) * (L : ℤ))
    simpa only [harg j] using h
  have hgsumm : Summable fun j : ℕ => C₀ / M ^ 2 * jbDecay 12 (t + (j : ℝ) * lam) :=
    (jbDecay_nat_shift_summable_gen (N := 12) (by norm_num) hlam0 ht0).mul_left _
  have hfsumm : Summable fun j : ℕ => ‖d (r + (j : ℤ) * (L : ℤ))‖ :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hle hgsumm
  have hkey : lam⁻¹ = M * (L : ℝ)⁻¹ := by
    rw [hlam, div_eq_mul_inv, mul_inv_rev, inv_inv]
  calc ∑' j : ℕ, ‖d (r + (j : ℤ) * (L : ℤ))‖
      ≤ ∑' j : ℕ, C₀ / M ^ 2 * jbDecay 12 (t + (j : ℝ) * lam) :=
        Summable.tsum_le_tsum hle hfsumm hgsumm
    _ = C₀ / M ^ 2 * ∑' j : ℕ, jbDecay 12 (t + (j : ℝ) * lam) := by rw [tsum_mul_left]
    _ ≤ C₀ / M ^ 2 * ((2 : ℝ) ^ 60 * lam⁻¹ * jbDecay 11 t) :=
        mul_le_mul_of_nonneg_left hsum hC
    _ = C₀ / M ^ 2 * ((2 : ℝ) ^ 60 * M / (L : ℝ)) * jbDecay 11 ((r : ℝ) / M) := by
        rw [ht, hkey, div_eq_mul_inv]
        ring

/-- **The half-line sum along a residue class, negative direction.**  The mirror image of
`box_halfSum_pos`, applied to the reflected progression `r, r − L, r − 2L, …` with `r < 0`. -/
theorem box_halfSum_neg (L : ℕ) (M C₀ : ℝ) (hL : 1 ≤ L) (hM : 0 < M) (hLM : (L : ℝ) ≤ M)
    (hC₀ : 0 < C₀) (d : ℤ → ℂ)
    (hd : ∀ n : ℤ, ‖d n‖ ≤ C₀ / M ^ 2 * jbDecay 12 ((n : ℝ) / M)) (r : ℤ) (hr : r < 0) :
    (∑' j : ℕ, ‖d (r - (j : ℤ) * (L : ℤ))‖)
      ≤ C₀ / M ^ 2 * ((2 : ℝ) ^ 60 * M / (L : ℝ)) * jbDecay 11 ((r : ℝ) / M) := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hrneg : (r : ℝ) < 0 := by exact_mod_cast hr
  set lam : ℝ := (L : ℝ) / M with hlam
  set t : ℝ := -((r : ℝ) / M) with ht
  have hlam0 : 0 < lam := by rw [hlam]; exact div_pos hLpos hM
  have hlam1 : lam ≤ 1 := by rw [hlam, div_le_one hM]; exact hLM
  have ht0 : 0 ≤ t := by
    rw [ht]
    have hrm : (r : ℝ) / M ≤ 0 := div_nonpos_of_nonpos_of_nonneg hrneg.le hM.le
    linarith
  have hC : (0 : ℝ) ≤ C₀ / M ^ 2 := by positivity
  have hsum := jbDecay_nat_shift_lattice_le_gen (n := 11) (by norm_num) hlam0 hlam1 ht0
  have harg : ∀ j : ℕ,
      (((r - (j : ℤ) * (L : ℤ) : ℤ)) : ℝ) / M = -(t + (j : ℝ) * lam) := by
    intro j
    rw [ht, hlam]
    push_cast
    ring
  have hle : ∀ j : ℕ, ‖d (r - (j : ℤ) * (L : ℤ))‖
      ≤ C₀ / M ^ 2 * jbDecay 12 (t + (j : ℝ) * lam) := by
    intro j
    have h := hd (r - (j : ℤ) * (L : ℤ))
    rw [harg j, jbDecay_neg] at h
    exact h
  have hgsumm : Summable fun j : ℕ => C₀ / M ^ 2 * jbDecay 12 (t + (j : ℝ) * lam) :=
    (jbDecay_nat_shift_summable_gen (N := 12) (by norm_num) hlam0 ht0).mul_left _
  have hfsumm : Summable fun j : ℕ => ‖d (r - (j : ℤ) * (L : ℤ))‖ :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hle hgsumm
  have hkey : lam⁻¹ = M * (L : ℝ)⁻¹ := by
    rw [hlam, div_eq_mul_inv, mul_inv_rev, inv_inv]
  calc ∑' j : ℕ, ‖d (r - (j : ℤ) * (L : ℤ))‖
      ≤ ∑' j : ℕ, C₀ / M ^ 2 * jbDecay 12 (t + (j : ℝ) * lam) :=
        Summable.tsum_le_tsum hle hfsumm hgsumm
    _ = C₀ / M ^ 2 * ∑' j : ℕ, jbDecay 12 (t + (j : ℝ) * lam) := by rw [tsum_mul_left]
    _ ≤ C₀ / M ^ 2 * ((2 : ℝ) ^ 60 * lam⁻¹ * jbDecay 11 t) :=
        mul_le_mul_of_nonneg_left hsum hC
    _ = C₀ / M ^ 2 * ((2 : ℝ) ^ 60 * M / (L : ℝ)) * jbDecay 11 ((r : ℝ) / M) := by
        rw [ht, jbDecay_neg, hkey, div_eq_mul_inv]
        ring

/-! ## The sliding-window decomposition -/

/-- **Sliding-window decomposition of a decaying sequence into interval indicators.** -/
theorem boxDecomp : ∃ C' : ℝ, 0 < C' ∧ ∀ (w : ℤ → ℂ) (L : ℕ) (M C₀ C₁ : ℝ),
    0 < C₀ → 0 < C₁ → 1 ≤ M → 1 ≤ L → (L : ℝ) ≤ M →
    (∀ n : ℤ, ‖w n - w (n - 1)‖ ≤ C₀ / M ^ 2 * jbDecay 12 ((n : ℝ) / M)) →
    (∀ n : ℤ, ‖w n‖ ≤ C₁ / M * jbDecay 12 ((n : ℝ) / M)) →
    (∀ r : ℤ, (∑' j : ℤ, (w (r + j * (L : ℤ)) - w (r + j * (L : ℤ) - 1))) = 0) →
    ∃ ρ : ℤ → ℂ, Summable (fun k : ℤ => ‖ρ k‖) ∧
        (∑' k : ℤ, ‖ρ k‖) ≤ C' * (C₀ + C₁) / L ∧
      ∀ n : ℤ, (∑' k : ℤ, ρ k * (if k ≤ n ∧ n ≤ k + (L : ℤ) - 1 then (1 : ℂ) else 0)) = w n := by
  refine ⟨(2 : ℝ) ^ 200, by norm_num, ?_⟩
  intro w L M C₀ C₁ hC₀ hC₁ hM hL hLM hdec hw hcl
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hLR : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < (L : ℝ) := lt_of_lt_of_le zero_lt_one hLR
  have hLne : ((L : ℤ)) ≠ 0 := by
    have : L ≠ 0 := by omega
    exact_mod_cast this
  set d : ℤ → ℂ := fun n => w n - w (n - 1) with hd
  have hddec : ∀ n : ℤ, ‖d n‖ ≤ C₀ / M ^ 2 * jbDecay 12 ((n : ℝ) / M) := by
    intro n; rw [hd]; exact hdec n
  have hd12 : Summable fun n : ℤ => jbDecay 12 ((n : ℝ) / M) :=
    jbDecay_int_summable_div (by norm_num : 12 ≤ 12) hMpos
  have hd11 : Summable fun n : ℤ => jbDecay 11 ((n : ℝ) / M) :=
    summable_jbDecay_eleven_int_div hMpos
  have hdtsum : Summable fun n : ℤ => ‖d n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hddec n) (hd12.mul_left _)
  have hds : Summable d := hdtsum.of_norm
  have hws : Summable w :=
    (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hw n) (hd12.mul_left _)).of_norm
  -- the class sums vanish
  have hsum0 : ∀ r : ℤ, (∑' j : ℤ, d (r + j * (L : ℤ))) = 0 := by
    intro r
    have hc : (∑' j : ℤ, d (r + j * (L : ℤ)))
        = ∑' j : ℤ, (w (r + j * (L : ℤ)) - w (r + j * (L : ℤ) - 1)) :=
      tsum_congr (fun j => by rw [hd])
    rw [hc]; exact hcl r
  -- the injections of the three parameterisations of a lattice
  have hinjB : ∀ r : ℤ, Function.Injective fun j : ℕ => r - (j : ℤ) * (L : ℤ) := by
    intro r a b hab
    have h1 : (a : ℤ) * (L : ℤ) = (b : ℤ) * (L : ℤ) := by linarith
    have h2 : (a : ℤ) = (b : ℤ) := mul_right_cancel₀ hLne h1
    exact_mod_cast h2
  have hinjF : ∀ r : ℤ, Function.Injective fun j : ℕ => r + (j : ℤ) * (L : ℤ) := by
    intro r a b hab
    have h1 : (a : ℤ) * (L : ℤ) = (b : ℤ) * (L : ℤ) := by linarith
    have h2 : (a : ℤ) = (b : ℤ) := mul_right_cancel₀ hLne h1
    exact_mod_cast h2
  have hinjN : ∀ r : ℤ, Function.Injective fun j : ℕ => r + (-((j : ℤ) + 1)) * (L : ℤ) := by
    intro r a b hab
    have h1 : (-((a : ℤ) + 1)) * (L : ℤ) = (-((b : ℤ) + 1)) * (L : ℤ) := by linarith
    have h2 : -((a : ℤ) + 1) = -((b : ℤ) + 1) := mul_right_cancel₀ hLne h1
    omega
  -- the sliding weight
  set ρ : ℤ → ℂ := fun r => ∑' j : ℕ, d (r - (j : ℤ) * (L : ℤ)) with hρdef
  have hρsum : ∀ r : ℤ, Summable fun j : ℕ => d (r - (j : ℤ) * (L : ℤ)) :=
    fun r => hds.comp_injective (hinjB r)
  -- its backward form
  have hρback : ∀ r : ℤ, ρ r = d r + ∑' j : ℕ, d (r - ((j : ℤ) + 1) * (L : ℤ)) := by
    intro r
    simp only [hρdef]
    rw [Summable.tsum_eq_zero_add (hρsum r)]
    have h0 : d (r - (((0 : ℕ)) : ℤ) * (L : ℤ)) = d r := by norm_num
    have hs : (∑' b : ℕ, d (r - (((b + 1 : ℕ)) : ℤ) * (L : ℤ)))
        = ∑' j : ℕ, d (r - ((j : ℤ) + 1) * (L : ℤ)) :=
      tsum_congr (fun j => by congr 1)
    rw [h0, hs]
  -- its forward form (uses the vanishing of the class sums)
  have hforward : ∀ r : ℤ, ρ r = d r - ∑' j : ℕ, d (r + (j : ℤ) * (L : ℤ)) := by
    intro r
    have hsplit : (∑' j : ℤ, d (r + j * (L : ℤ)))
        = (∑' j : ℕ, d (r + (j : ℤ) * (L : ℤ)))
          + (∑' j : ℕ, d (r + (-((j : ℤ) + 1)) * (L : ℤ))) :=
      tsum_of_nat_of_neg_add_one (f := fun j : ℤ => d (r + j * (L : ℤ)))
        (hds.comp_injective (hinjF r)) (hds.comp_injective (hinjN r))
    have h0 : (∑' j : ℕ, d (r + (j : ℤ) * (L : ℤ)))
        + (∑' j : ℕ, d (r + (-((j : ℤ) + 1)) * (L : ℤ))) = 0 := by
      rw [← hsplit, hsum0 r]
    have htail : (∑' j : ℕ, d (r + (-((j : ℤ) + 1)) * (L : ℤ))) = ρ r - d r := by
      have hcanon : (∑' j : ℕ, d (r + (-((j : ℤ) + 1)) * (L : ℤ)))
          = ∑' j : ℕ, d (r - ((j : ℤ) + 1) * (L : ℤ)) :=
        tsum_congr (fun j => by congr 1)
      rw [hcanon, hρback r]
      ring
    rw [htail] at h0
    have hneg : ρ r - d r = -(∑' j : ℕ, d (r + (j : ℤ) * (L : ℤ))) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact h0
    have hcongr : ρ r = -(∑' j : ℕ, d (r + (j : ℤ) * (L : ℤ))) + d r := by
      simpa using congrArg (fun z => z + d r) hneg
    rw [hcongr]; ring
  -- the pointwise bound on `ρ`
  have hρbound : ∀ r : ℤ, ‖ρ r‖
      ≤ C₀ / M ^ 2 * (jbDecay 12 ((r : ℝ) / M)
          + ((2 : ℝ) ^ 60 * M / (L : ℝ)) * jbDecay 11 ((r : ℝ) / M)) := by
    intro r
    by_cases hr : 0 ≤ r
    · rw [hforward r]
      have h1 : ‖d r‖ ≤ C₀ / M ^ 2 * jbDecay 12 ((r : ℝ) / M) := hddec r
      have h2 := box_halfSum_pos L M C₀ hL hMpos hLM hC₀ d hddec r hr
      have h3 : ‖∑' j : ℕ, d (r + (j : ℤ) * (L : ℤ))‖
          ≤ ∑' j : ℕ, ‖d (r + (j : ℤ) * (L : ℤ))‖ :=
        norm_tsum_le_tsum_norm (hdtsum.comp_injective (hinjF r))
      calc ‖d r - ∑' j : ℕ, d (r + (j : ℤ) * (L : ℤ))‖
          ≤ ‖d r‖ + ‖∑' j : ℕ, d (r + (j : ℤ) * (L : ℤ))‖ := norm_sub_le _ _
        _ ≤ C₀ / M ^ 2 * jbDecay 12 ((r : ℝ) / M)
              + C₀ / M ^ 2 * ((2 : ℝ) ^ 60 * M / (L : ℝ)) * jbDecay 11 ((r : ℝ) / M) := by
            linarith
        _ = C₀ / M ^ 2 * (jbDecay 12 ((r : ℝ) / M)
              + ((2 : ℝ) ^ 60 * M / (L : ℝ)) * jbDecay 11 ((r : ℝ) / M)) := by ring
    · have hr0 : r < 0 := by omega
      have h3 : ‖ρ r‖ ≤ ∑' j : ℕ, ‖d (r - (j : ℤ) * (L : ℤ))‖ := by
        rw [hρdef]
        exact norm_tsum_le_tsum_norm (hdtsum.comp_injective (hinjB r))
      have h2 := box_halfSum_neg L M C₀ hL hMpos hLM hC₀ d hddec r hr0
      have hc : (0 : ℝ) < C₀ / M ^ 2 := by positivity
      have hj12 : (0 : ℝ) ≤ jbDecay 12 ((r : ℝ) / M) := jbDecay_nonneg _ _
      calc ‖ρ r‖ ≤ C₀ / M ^ 2 * ((2 : ℝ) ^ 60 * M / (L : ℝ)) * jbDecay 11 ((r : ℝ) / M) :=
            h3.trans h2
        _ = C₀ / M ^ 2 * (((2 : ℝ) ^ 60 * M / (L : ℝ)) * jbDecay 11 ((r : ℝ) / M)) := by ring
        _ ≤ C₀ / M ^ 2 * (jbDecay 12 ((r : ℝ) / M)
              + ((2 : ℝ) ^ 60 * M / (L : ℝ)) * jbDecay 11 ((r : ℝ) / M)) := by
            refine mul_le_mul_of_nonneg_left ?_ hc.le
            linarith
  -- summability of the majorant and of `ρ`
  have hmaj : Summable fun r : ℤ =>
      C₀ / M ^ 2 * (jbDecay 12 ((r : ℝ) / M)
        + ((2 : ℝ) ^ 60 * M / (L : ℝ)) * jbDecay 11 ((r : ℝ) / M)) :=
    Summable.mul_left _ (Summable.add hd12 (hd11.mul_left _))
  have hρsummn : Summable fun k : ℤ => ‖ρ k‖ :=
    Summable.of_nonneg_of_le (fun r => norm_nonneg _) hρbound hmaj
  have hρsumm : Summable ρ := hρsummn.of_norm
  -- the `ℓ¹` bound
  have htotal : (∑' k : ℤ, ‖ρ k‖) ≤ (2 : ℝ) ^ 200 * (C₀ + C₁) / L := by
    have hb1 := Summable.tsum_le_tsum hρbound hρsummn hmaj
    have h1 : (∑' r : ℤ, C₀ / M ^ 2 * (jbDecay 12 ((r : ℝ) / M)
          + ((2 : ℝ) ^ 60 * M / (L : ℝ)) * jbDecay 11 ((r : ℝ) / M)))
        = C₀ / M ^ 2 * ((∑' r : ℤ, jbDecay 12 ((r : ℝ) / M))
            + ((2 : ℝ) ^ 60 * M / (L : ℝ)) * (∑' r : ℤ, jbDecay 11 ((r : ℝ) / M))) := by
      rw [tsum_mul_left, Summable.tsum_add hd12 (hd11.mul_left _), tsum_mul_left]
    rw [h1] at hb1
    have hb12 := jbDecay_int_lattice_le_div (N := 12) (by norm_num) hM
    have hb11 := jbDecay_int_lattice_le11 hM
    have hA : C₀ / M ^ 2 * ((∑' r : ℤ, jbDecay 12 ((r : ℝ) / M))
          + ((2 : ℝ) ^ 60 * M / (L : ℝ)) * (∑' r : ℤ, jbDecay 11 ((r : ℝ) / M)))
        ≤ C₀ * (2 ^ 61 / M + 2 ^ 121 / (L : ℝ)) := by
      have hstep : C₀ / M ^ 2 * ((∑' r : ℤ, jbDecay 12 ((r : ℝ) / M))
            + ((2 : ℝ) ^ 60 * M / (L : ℝ)) * (∑' r : ℤ, jbDecay 11 ((r : ℝ) / M)))
          ≤ C₀ / M ^ 2 * ((2 * ((2 : ℝ) ^ 60 * M))
              + ((2 : ℝ) ^ 60 * M / (L : ℝ)) * (2 * ((2 : ℝ) ^ 60 * M))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hc2 : (0 : ℝ) ≤ (2 : ℝ) ^ 60 * M / (L : ℝ) := by positivity
        have h1 := mul_le_mul_of_nonneg_left hb11 hc2
        linarith
      refine hstep.trans (le_of_eq ?_)
      field_simp
    refine (hb1.trans hA).trans ?_
    have hb : C₀ * (2 ^ 61 / M + 2 ^ 121 / (L : ℝ)) ≤ (2 : ℝ) ^ 200 * (C₀ + C₁) / (L : ℝ) := by
      have hdiv : (2 : ℝ) ^ 61 / M ≤ (2 : ℝ) ^ 61 / (L : ℝ) :=
        div_le_div_of_nonneg_left (by norm_num) hLpos hLM
      have hsum : C₀ * (2 ^ 61 / M + 2 ^ 121 / (L : ℝ))
          ≤ C₀ * ((2 ^ 61 + 2 ^ 121) / (L : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hC₀.le
        rw [add_div]
        linarith
      refine hsum.trans ?_
      rw [← mul_div_assoc]
      refine div_le_div_of_nonneg_right ?_ hLpos.le
      have h4 : (2 : ℝ) ^ 61 + 2 ^ 121 ≤ 2 ^ 200 := by norm_num
      nlinarith [hC₀.le, hC₁.le, h4]
    exact hb
  exact ⟨ρ, hρsummn, htotal, fun n => slideSum_eq w L hL hws ρ (fun r => by simp only [hρdef, hd]) n⟩

end Work.KMTAreas.A4
