import Mathlib
import Submission.Work.ZeroDensity.Jutila.bvDefs

namespace Work.LinnikAreas2

open Finset
open Work.ZeroDensity.Jutila (Lz)

noncomputable section

/-!
# Sharp `Λ_z²` second moment for a real cutoff, from the two integer-cutoff ranges

`Lz z n = Σ_{d ∣ n, d ≤ z} μ(d)·log(z/d)` (Jutila's truncated von Mangoldt sum, `bvDefs.lean`).
-/

/-- `Lz` with a real cutoff in `[k, k+1)` as an explicit sum over the divisors `≤ k`. -/
private lemma Lz_eq_sum_shift {k : ℕ} {z : ℝ} (hz1 : (k:ℝ) ≤ z) (hz2 : z < ((k+1:ℕ):ℝ))
    (n : ℕ) :
    Lz z n = ∑ d ∈ n.divisors.filter (fun d : ℕ => d ≤ k),
      (ArithmeticFunction.moebius d : ℝ) * (Real.log z - Real.log d) := by
  rw [Lz]
  rw [Finset.filter_congr (p := fun d : ℕ => (d:ℝ) ≤ z) (q := fun d : ℕ => d ≤ k)]
  · refine Finset.sum_congr rfl (fun d hd => ?_)
    obtain ⟨hdmem, hdk⟩ := Finset.mem_filter.mp hd
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hdmem).1
    have hdne : d ≠ 0 := fun h =>
      (Nat.mem_divisors.mp hdmem).2 (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))
    have hd1 : 1 ≤ d := Nat.pos_of_ne_zero hdne
    have hzpos : 0 < z := by
      have h1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd1
      have h2 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast (le_trans hd1 hdk)
      linarith
    rw [Real.log_div (ne_of_gt hzpos) (by exact_mod_cast hdne), mul_sub]
  · intro d _
    constructor
    · intro hd
      have h : (d:ℝ) < ((k+1:ℕ):ℝ) := lt_of_le_of_lt hd hz2
      have h' : d < k+1 := by exact_mod_cast h
      omega
    · intro hd
      have h : (d:ℝ) ≤ (k:ℝ) := by exact_mod_cast hd
      linarith

/-- The sum over the divisors `≤ k+1` collapses to the sum over those `≤ k` when the term at
`k+1` vanishes. -/
private lemma sum_filter_succ_eq (k n : ℕ) (F : ℕ → ℝ) (hF : F (k+1) = 0) :
    (∑ d ∈ n.divisors.filter (fun d : ℕ => d ≤ k+1), F d)
      = ∑ d ∈ n.divisors.filter (fun d : ℕ => d ≤ k), F d := by
  have hsplit : (∑ d ∈ n.divisors.filter (fun d : ℕ => d ≤ k+1), F d)
      = (∑ d ∈ n.divisors.filter (fun d : ℕ => d ≤ k), F d)
        + (∑ d ∈ n.divisors.filter (fun d : ℕ => d = k+1), F d) := by
    rw [← Finset.sum_union (s₁ := n.divisors.filter (fun d : ℕ => d ≤ k))
          (s₂ := n.divisors.filter (fun d : ℕ => d = k+1)) ?_]
    · congr 1
      ext d
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hd, hle⟩
        rcases Nat.lt_or_ge d (k+1) with h | h
        · exact Or.inl ⟨hd, by omega⟩
        · exact Or.inr ⟨hd, by omega⟩
      · rintro (⟨hd, hk⟩ | ⟨hd, hk⟩)
        · exact ⟨hd, by omega⟩
        · exact ⟨hd, by omega⟩
    · rw [Finset.disjoint_left]
      intro d hd1 hd2
      simp only [Finset.mem_filter] at hd1 hd2
      omega
  have hzero : (∑ d ∈ n.divisors.filter (fun d : ℕ => d = k+1), F d) = 0 := by
    refine Finset.sum_eq_zero (fun d hd => ?_)
    obtain ⟨hd1, hd2⟩ := Finset.mem_filter.mp hd
    rw [hd2]; exact hF
  rw [hsplit, hzero, add_zero]

/-- Affine combination of sums of an affine function of a real parameter. -/
private lemma affine_comb_sums {ι : Type*} (s : Finset ι) (c L : ι → ℝ) {A B α : ℝ}
    (hAB : B - A ≠ 0) :
    (∑ d ∈ s, c d * (α - L d)) =
      ((B - α)/(B - A)) * (∑ d ∈ s, c d * (A - L d))
      + ((α - A)/(B - A)) * (∑ d ∈ s, c d * (B - L d)) := by
  have hsc : ∀ x : ℝ, ((B - α)/(B - A))*(A - x) + ((α - A)/(B - A))*(B - x) = α - x := by
    intro x; field_simp; ring
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [← hsc (L d)]
  ring

/-- **Real cutoff = affine interpolation of the two neighbouring integer cutoffs.**

For `k ≤ z < k+1` and `k ≥ 1`, and with `θ = (log(k+1) − log z)/(log(k+1) − log k)`,
`Lz z n = θ·Lz k n + (1−θ)·Lz (k+1) n`. -/
private lemma Lz_affine_interp (k : ℕ) (hk : 1 ≤ k) (z : ℝ) (hz1 : (k:ℝ) ≤ z)
    (hz2 : z < ((k+1:ℕ):ℝ)) (n : ℕ) :
    Lz z n =
      ((Real.log ((k+1:ℕ):ℝ) - Real.log z) / (Real.log ((k+1:ℕ):ℝ) - Real.log (k:ℝ)))
        * Lz (k:ℝ) n
      + ((Real.log z - Real.log (k:ℝ)) / (Real.log ((k+1:ℕ):ℝ) - Real.log (k:ℝ)))
        * Lz ((k+1:ℕ):ℝ) n := by
  have hz : Lz z n = ∑ d ∈ n.divisors.filter (fun d : ℕ => d ≤ k),
      (ArithmeticFunction.moebius d : ℝ) * (Real.log z - Real.log d) :=
    Lz_eq_sum_shift hz1 hz2 n
  have hk : Lz (k:ℝ) n = ∑ d ∈ n.divisors.filter (fun d : ℕ => d ≤ k),
      (ArithmeticFunction.moebius d : ℝ) * (Real.log (k:ℝ) - Real.log d) :=
    Lz_eq_sum_shift (k := k) (z := (k:ℝ)) le_rfl (by push_cast; linarith) n
  have hk1 : Lz ((k+1:ℕ):ℝ) n = ∑ d ∈ n.divisors.filter (fun d : ℕ => d ≤ k),
      (ArithmeticFunction.moebius d : ℝ) * (Real.log ((k+1:ℕ):ℝ) - Real.log d) := by
    have hz2' : ((k+1:ℕ):ℝ) < (((k+1)+1:ℕ):ℝ) := by push_cast; linarith
    rw [Lz_eq_sum_shift (k := k+1) (z := ((k+1:ℕ):ℝ)) le_rfl hz2']
    exact sum_filter_succ_eq k n _ (by
      show (ArithmeticFunction.moebius (k+1) : ℝ) *
        (Real.log ((k+1:ℕ):ℝ) - Real.log ((k+1:ℕ):ℝ)) = 0
      rw [sub_self, mul_zero])
  have hAB : Real.log ((k+1:ℕ):ℝ) - Real.log (k:ℝ) ≠ 0 := by
    have h : Real.log (k:ℝ) < Real.log ((k+1:ℕ):ℝ) :=
      Real.log_lt_log (by exact_mod_cast (by omega : 0 < k)) (by push_cast; linarith)
    linarith
  rw [hz, hk, hk1]
  exact affine_comb_sums _ _ _ hAB

/-- Convexity of the square at a convex combination. -/
private lemma sq_le_convex_comb {θ ψ a b : ℝ} (h0 : 0 ≤ θ) (h1 : 0 ≤ ψ) (hs : θ + ψ = 1) :
    (θ * a + ψ * b) ^ 2 ≤ θ * a ^ 2 + ψ * b ^ 2 := by
  have hψ : ψ = 1 - θ := by linarith
  rw [hψ]
  nlinarith [mul_nonneg h0 (by linarith : (0:ℝ) ≤ 1 - θ), sq_nonneg (a - b)]

/-- **Sharp `Λ_z²` second moment for a real cutoff, from the two integer-cutoff ranges.**
`Lz z n = Σ_{d ∣ n, d ≤ z} μ(d)·log(z/d)`. Given the sharp integer-cutoff bounds (easy range `z² ≤ N` and
hard range `z ≤ N < z²`), deduce the same sharp bound for every *real* cutoff `z ≥ 2` and every `N ≥ z`:
the divisors of `n` below the real cutoff `z` are those `≤ ⌊z⌋`, and on `[k, k+1)` the sum `Lz z n` is the
affine interpolation (in `log z`) of the integer-cutoff values `Lz k n`, `Lz (k+1) n`; convexity of `x ↦ x²`
and the exact identity `θ·log k + (1−θ)·log(k+1) = log z` transfer the integer bounds without loss of the
leading constant. (The case where `k + 1 > N`, i.e. `z ∈ [N, N+1)`, is handled directly, since then every
divisor of `n ≤ N` is `≤ z` and `Lz z n = Λ n + [n = 1]·log z`.) -/
theorem lz_sq_sharp_real_of_int
    (hE : ∃ C : ℝ, 0 < C ∧ ∀ (z N : ℕ), 2 ≤ z → z ≤ N → z * z ≤ N →
      (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Lz (z : ℝ) n) ^ 2)
        ≤ (N : ℝ) * Real.log (z : ℝ) + C * (N : ℝ))
    (hH : ∃ C : ℝ, 0 < C ∧ ∀ (z N : ℕ), 2 ≤ z → z ≤ N → N < z * z →
      (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Lz (z : ℝ) n) ^ 2)
        ≤ (N : ℝ) * Real.log (z : ℝ) + C * (N : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : ℝ), 2 ≤ z → ∀ N : ℕ, z ≤ (N : ℝ) →
      (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Lz z n) ^ 2)
        ≤ (N : ℝ) * Real.log z + C * (N : ℝ) := by
  obtain ⟨CE, hCE, hE'⟩ := hE
  obtain ⟨CH, hCH, hH'⟩ := hH
  refine ⟨max CE CH, lt_max_of_lt_left hCE, ?_⟩
  have hInt : ∀ (z N : ℕ), 2 ≤ z → z ≤ N →
      (∑ n ∈ Finset.Icc 1 N, (Lz (z : ℝ) n) ^ 2)
        ≤ (N : ℝ) * Real.log (z : ℝ) + max CE CH * (N : ℝ) := by
    intro z N hz hzN
    rcases le_or_gt (z * z) N with h | h
    · have hb := hE' z N hz hzN h
      have hle : CE * (N : ℝ) ≤ max CE CH * (N : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg N)
      linarith
    · have hb := hH' z N hz hzN h
      have hle : CH * (N : ℝ) ≤ max CE CH * (N : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg N)
      linarith
  intro z hz N hzN
  set k := ⌊z⌋₊ with hkdef
  have hk2 : 2 ≤ k := Nat.le_floor (by exact_mod_cast hz)
  have hkz : (k:ℝ) ≤ z := Nat.floor_le (by linarith)
  have hzk1 : z < ((k+1:ℕ):ℝ) := by
    have h := Nat.lt_floor_add_one z
    rw [← hkdef] at h
    push_cast
    linarith
  have hk1 : 1 ≤ k := by omega
  set A : ℝ := Real.log (k:ℝ) with hA
  set B : ℝ := Real.log ((k+1:ℕ):ℝ) with hB
  set α : ℝ := Real.log z with hα
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hzpos : (0:ℝ) < z := by linarith
  have hAα : A ≤ α := by rw [hA, hα]; exact Real.log_le_log hkpos hkz
  have hαB : α < B := by rw [hα, hB]; exact Real.log_lt_log hzpos hzk1
  have hAB : 0 < B - A := by linarith
  have hθ0 : 0 ≤ (B - α) / (B - A) := div_nonneg (by linarith) (le_of_lt hAB)
  have hψ0 : 0 ≤ (α - A) / (B - A) := div_nonneg (by linarith) (le_of_lt hAB)
  have hsumθ : (B - α) / (B - A) + (α - A) / (B - A) = 1 := by field_simp; ring
  have hcomb : ((B - α) / (B - A)) * A + ((α - A) / (B - A)) * B = α := by
    field_simp; ring
  have hterm : ∀ n : ℕ, (Lz z n) ^ 2 ≤
      ((B - α) / (B - A)) * (Lz (k:ℝ) n) ^ 2
        + ((α - A) / (B - A)) * (Lz ((k+1:ℕ):ℝ) n) ^ 2 := by
    intro n
    have hinterp := Lz_affine_interp k hk1 z hkz hzk1 n
    rw [← hA, ← hB, ← hα] at hinterp
    rw [hinterp]
    exact sq_le_convex_comb hθ0 hψ0 hsumθ
  have hsumle : (∑ n ∈ Finset.Icc 1 N, (Lz z n) ^ 2) ≤
      ((B - α) / (B - A)) * (∑ n ∈ Finset.Icc 1 N, (Lz (k:ℝ) n) ^ 2)
        + ((α - A) / (B - A)) * (∑ n ∈ Finset.Icc 1 N, (Lz ((k+1:ℕ):ℝ) n) ^ 2) := by
    calc (∑ n ∈ Finset.Icc 1 N, (Lz z n) ^ 2)
        ≤ ∑ n ∈ Finset.Icc 1 N, (((B - α) / (B - A)) * (Lz (k:ℝ) n) ^ 2
            + ((α - A) / (B - A)) * (Lz ((k+1:ℕ):ℝ) n) ^ 2) :=
          Finset.sum_le_sum (fun n _ => hterm n)
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rcases eq_or_lt_of_le hkz with hzk | hzk
  · have hkN : k ≤ N := by
      have h' : (k:ℝ) ≤ (N:ℝ) := by rw [hzk]; exact hzN
      exact_mod_cast h'
    have hkeq : (∑ n ∈ Finset.Icc 1 N, (Lz z n) ^ 2)
        = ∑ n ∈ Finset.Icc 1 N, (Lz (k:ℝ) n) ^ 2 := by
      apply Finset.sum_congr rfl
      intro n _
      rw [hzk]
    rw [hkeq, hα, ← hzk]
    exact hInt k N hk2 hkN
  · have hkN : k ≤ N := by
      have h' : (k:ℝ) ≤ (N:ℝ) := le_trans (le_of_lt hzk) hzN
      exact_mod_cast h'
    have hk1N : k + 1 ≤ N := by
      have hlt : k < N := by
        have h' : (k:ℝ) < (N:ℝ) := lt_of_lt_of_le hzk hzN
        exact_mod_cast h'
      omega
    have hIntk := hInt k N hk2 hkN
    have hIntk1 := hInt (k+1) N (by omega) hk1N
    have hb1 := mul_le_mul_of_nonneg_left hIntk hθ0
    have hb2 := mul_le_mul_of_nonneg_left hIntk1 hψ0
    have hcomb' : ((B - α) / (B - A)) * Real.log (k:ℝ)
        + ((α - A) / (B - A)) * Real.log ((k+1:ℕ):ℝ) = Real.log z := by
      rw [← hA, ← hB, ← hα]
      exact hcomb
    have e : ((B - α) / (B - A)) * ((N:ℝ) * Real.log (k:ℝ) + max CE CH * (N:ℝ))
        + ((α - A) / (B - A)) * ((N:ℝ) * Real.log ((k+1:ℕ):ℝ) + max CE CH * (N:ℝ))
        = (N:ℝ) * Real.log z + max CE CH * (N:ℝ) := by
      linear_combination (N:ℝ) * hcomb' + (max CE CH * (N:ℝ)) * hsumθ
    nlinarith [hsumle, hb1, hb2, e]

end

end Work.LinnikAreas2
