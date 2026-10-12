import Mathlib.Analysis.PSeries
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.NormEqKcast
import Submission.Work.BoseBoxFock.ShellCard
import Submission.Work.BoseBoxFock.farK0_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary lemmas for the sharp lattice tail bound

Helpers for `Work.BoseBoxFock.PCFU.latTailNSqBound`:
`nSq d = Σ_i (d i).natAbs ^ 2` is the squared Euclidean norm of the lattice vector, and
`K d = max_i |d i|` is its sup-norm.  The two basic comparisons are

* `latTailNSqAux_K_sq_le_nSq` : `(K d) ^ 2 ≤ nSq d` (a coordinate realises the sup),
* `latTailNSqAux_nSq_le_three_mul_K_sq` : `(nSq d : ℝ) ≤ 3 * (K d) ^ 2` (three coordinates).

The threshold `K₀ = max 1 ⌈ρ/3⌉₊` then dominates `ρ/3` from above
(`latTailNSqAux_rho_le_three_mul`) and is dominated by `K d` whenever `ρ ^ 2 < nSq d`
(`latTailNSqAux_one_le_K`, `latTailNSqAux_ceil_third_le_K`), which is all the shell
decomposition needs.
-/

namespace Work.BoseBoxFock.PCFU

open Finset

noncomputable section

/-- A coordinate realises the sup-norm, so `(K d) ^ 2 ≤ nSq d`. -/
lemma latTailNSqAux_K_sq_le_nSq (d : Fin 3 → ℤ) : (K d) ^ 2 ≤ nSq d := by
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin 3)) ⟨0, Finset.mem_univ 0⟩
      fun j => (d j).natAbs
  rw [K, hi]
  exact coord_sq_le_nSq d i

/-- `(nSq d : ℝ) ≤ 3 * (K d) ^ 2`. -/
lemma latTailNSqAux_nSq_le_three_mul_K_sq (d : Fin 3 → ℤ) :
    (nSq d : ℝ) ≤ 3 * ((K d : ℕ) : ℝ) ^ 2 := by
  rw [nSq_cast]
  have h : ∀ i : Fin 3, ((d i : ℤ) : ℝ) ^ 2 ≤ ((K d : ℕ) : ℝ) ^ 2 := by
    intro i
    rw [← cast_natAbs_sq (d i)]
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast K_spec d i) 2
  calc ∑ i, ((d i : ℤ) : ℝ) ^ 2 ≤ ∑ _i : Fin 3, ((K d : ℕ) : ℝ) ^ 2 :=
        Finset.sum_le_sum fun i _ => h i
    _ = 3 * ((K d : ℕ) : ℝ) ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- If `ρ ≥ 1` and `ρ ^ 2 < nSq d` then `1 ≤ K d` (the vector is nonzero). -/
lemma latTailNSqAux_one_le_K (ρ : ℝ) (_hρ : 1 ≤ ρ) (d : Fin 3 → ℤ)
    (hd : ρ ^ 2 < (nSq d : ℝ)) : 1 ≤ K d := by
  rcases Nat.eq_zero_or_pos (K d) with h | h
  · exfalso
    have hd0 : d = 0 := eq_zero_of_K_eq_zero h
    rw [hd0] at hd
    simp only [nSq_zero, Nat.cast_zero] at hd
    nlinarith
  · exact h

/-- If `ρ ≥ 1` and `ρ ^ 2 < nSq d` then `⌈ρ / 3⌉₊ ≤ K d`. -/
lemma latTailNSqAux_ceil_third_le_K (ρ : ℝ) (hρ : 1 ≤ ρ) (d : Fin 3 → ℤ)
    (hd : ρ ^ 2 < (nSq d : ℝ)) : ⌈ρ / 3⌉₊ ≤ K d := by
  refine Nat.ceil_le.mpr ?_
  have hle := latTailNSqAux_nSq_le_three_mul_K_sq d
  have h1 : ρ ^ 2 < 3 * ((K d : ℕ) : ℝ) ^ 2 := lt_of_lt_of_le hd hle
  have hKnn : (0 : ℝ) ≤ (K d : ℕ) := Nat.cast_nonneg _
  have h3 : ρ < 3 * (K d : ℝ) := by
    by_contra hcon
    push Not at hcon
    nlinarith [hcon, hKnn, h1]
  linarith

/-- `ρ ≤ 3 * max 1 ⌈ρ / 3⌉₊`. -/
lemma latTailNSqAux_rho_le_three_mul (ρ : ℝ) :
    ρ ≤ 3 * ((max 1 ⌈ρ / 3⌉₊ : ℕ) : ℝ) := by
  have h1 : ρ / 3 ≤ ((⌈ρ / 3⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h2 : ((⌈ρ / 3⌉₊ : ℕ) : ℝ) ≤ ((max 1 ⌈ρ / 3⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast le_max_right (1 : ℕ) ⌈ρ / 3⌉₊
  linarith

/-- The shell weight comparison: for `k ≥ 1`,

`(24 k² + 2) * ((k²) ^ N)⁻¹ ≤ 26 * (k ^ (2 * N - 2))⁻¹`.

(Since `(24 k² + 2) ≤ 26 k²` and `k² * (k ^ (2N))⁻¹ = (k ^ (2N - 2))⁻¹`.) -/
lemma latTailNSqAux_shellWeight_le (N k : ℕ) (hN : 1 ≤ N) (hk : 1 ≤ k) :
    (24 * (k : ℝ) ^ 2 + 2) * (((k : ℝ) ^ 2) ^ N)⁻¹
      ≤ 26 * ((k : ℝ) ^ (2 * N - 2))⁻¹ := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have h2N : 2 ≤ 2 * N := by omega
  have hk2pos : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  -- the power bookkeeping: `(k²)^N = k ^ (2N)` and `k ^ (2N) = k² * k ^ (2N-2)`
  have hpow : (((k : ℝ) ^ 2) ^ N) = (k : ℝ) ^ (2 * N) := by
    rw [← pow_mul, mul_comm]
  have hsplit : ((k : ℝ) ^ (2 * N))⁻¹
      = ((k : ℝ) ^ 2)⁻¹ * ((k : ℝ) ^ (2 * N - 2))⁻¹ := by
    have h1 : ((k : ℝ) ^ (2 * N - 2))⁻¹ = (k : ℝ) ^ 2 * ((k : ℝ) ^ (2 * N))⁻¹ := by
      rw [pow_sub₀ (k : ℝ) (ne_of_gt hk0) h2N, mul_inv, inv_inv, mul_comm]
    rw [h1, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hk2pos), one_mul]
  have hstep : (24 * (k : ℝ) ^ 2 + 2) * ((k : ℝ) ^ 2)⁻¹ ≤ 26 := by
    have h24 : 24 * (k : ℝ) ^ 2 + 2 ≤ 26 * (k : ℝ) ^ 2 := by nlinarith
    rw [← div_eq_mul_inv, div_le_iff₀ hk2pos]
    linarith
  calc (24 * (k : ℝ) ^ 2 + 2) * (((k : ℝ) ^ 2) ^ N)⁻¹
      = (24 * (k : ℝ) ^ 2 + 2) * (((k : ℝ) ^ 2)⁻¹ * ((k : ℝ) ^ (2 * N - 2))⁻¹) := by
        rw [hpow, hsplit]
    _ = ((24 * (k : ℝ) ^ 2 + 2) * ((k : ℝ) ^ 2)⁻¹) * ((k : ℝ) ^ (2 * N - 2))⁻¹ := by ring
    _ ≤ 26 * ((k : ℝ) ^ (2 * N - 2))⁻¹ :=
        mul_le_mul_of_nonneg_right hstep (by positivity)

/-- **Shell reduction.**  A sum of `(nSq d) ^ (-N)` over lattice vectors with `nSq d > ρ ^ 2` and
sup-norm `K d` between `K₀` and `M` is dominated by the shell series
`∑_{k ∈ Ico K₀ (M+1)} (24 k² + 2) (k ^ (2N))⁻¹`. -/
theorem latTailNSqAux_shellSum (N : ℕ) (ρ : ℝ) (K₀ M : ℕ) (hK₀ : 1 ≤ K₀)
    (hKd : ∀ d : Fin 3 → ℤ, ρ ^ 2 < (nSq d : ℝ) → K₀ ≤ K d)
    (u : Finset (Fin 3 → ℤ)) (hMu : ∀ d ∈ u, K d ≤ M) :
    ∑ d ∈ u.filter (fun d => ρ ^ 2 < (nSq d : ℝ)), ((nSq d : ℝ) ^ N)⁻¹
      ≤ ∑ k ∈ Finset.Ico K₀ (M + 1), (24 * (k : ℝ) ^ 2 + 2) * ((k : ℝ) ^ (2 * N))⁻¹ := by
  classical
  set F := u.filter (fun d => ρ ^ 2 < (nSq d : ℝ)) with hF
  have hmaps : ∀ d ∈ F, K d ∈ Finset.Ico K₀ (M + 1) := by
    intro d hd
    rw [hF, Finset.mem_filter] at hd
    exact Finset.mem_Ico.mpr ⟨hKd d hd.2, Nat.lt_succ_of_le (hMu d hd.1)⟩
  rw [hF, ← Finset.sum_fiberwise_of_maps_to hmaps (fun d => ((nSq d : ℝ) ^ N)⁻¹)]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [Finset.mem_Ico] at hk
  have hk1 : 1 ≤ k := le_trans hK₀ hk.1
  have hsub : F.filter (fun d => K d = k) ⊆ shell k := by
    intro d hd
    rw [Finset.mem_filter] at hd
    rw [shell, Finset.mem_sdiff]
    exact ⟨mem_box_of_K_eq d k hd.2, not_mem_box_pred_of_K_eq hk1 hd.2⟩
  have hcard : ((F.filter (fun d => K d = k)).card : ℝ) ≤ 24 * (k : ℝ) ^ 2 + 2 := by
    have := le_trans (Finset.card_le_card hsub) (ShellCard hk1)
    exact_mod_cast this
  have hpt : ∀ d ∈ F.filter (fun d => K d = k),
      ((nSq d : ℝ) ^ N)⁻¹ ≤ ((k : ℝ) ^ (2 * N))⁻¹ := by
    intro d hd
    rw [Finset.mem_filter] at hd
    have hKk : K d = k := hd.2
    have h1 : k ^ 2 ≤ nSq d := by rw [← hKk]; exact latTailNSqAux_K_sq_le_nSq d
    have h2 : ((k : ℝ) ^ 2) ≤ (nSq d : ℝ) := by exact_mod_cast h1
    have h3 : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
    have h5 : (((k : ℝ) ^ 2) ^ N) ≤ ((nSq d : ℝ) ^ N) :=
      pow_le_pow_left₀ (le_of_lt h3) h2 N
    have h6 : (((k : ℝ) ^ 2) ^ N) = ((k : ℝ) ^ (2 * N)) := by rw [← pow_mul, mul_comm]
    have := (inv_le_inv₀ (pow_pos (lt_of_lt_of_le h3 h2) N) (pow_pos h3 N)).mpr h5
    rwa [h6] at this
  calc ∑ d ∈ F.filter (fun d => K d = k), ((nSq d : ℝ) ^ N)⁻¹
      ≤ ∑ _d ∈ F.filter (fun d => K d = k), ((k : ℝ) ^ (2 * N))⁻¹ := Finset.sum_le_sum hpt
    _ = ((F.filter (fun d => K d = k)).card : ℝ) * ((k : ℝ) ^ (2 * N))⁻¹ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (24 * (k : ℝ) ^ 2 + 2) * ((k : ℝ) ^ (2 * N))⁻¹ :=
        mul_le_mul_of_nonneg_right hcard (by positivity)

/-- **The `p`-series tail.**  For `q ≥ 2` and `K₀ ≥ 1`,
`∑_{k ∈ Ico K₀ M} k ^ (-q) ≤ 2 * (K₀ ^ (q-1))⁻¹`. -/
theorem latTailNSqAux_powTail (q : ℕ) (hq : 2 ≤ q) (K₀ M : ℕ) (hK₀ : 1 ≤ K₀) :
    ∑ k ∈ Finset.Ico K₀ M, ((k : ℝ) ^ q)⁻¹ ≤ 2 * (((K₀ : ℝ) ^ (q - 1))⁻¹) := by
  have hK₀0 : (0 : ℝ) < (K₀ : ℝ) := by exact_mod_cast hK₀
  have hpt : ∀ k ∈ Finset.Ioo (K₀ - 1) M,
      ((k : ℝ) ^ q)⁻¹ ≤ ((K₀ : ℝ) ^ (q - 2))⁻¹ * ((k : ℝ) ^ 2)⁻¹ := by
    intro k hk
    rw [Finset.mem_Ioo] at hk
    have hkK₀ : K₀ ≤ k := by omega
    have hk1 : 1 ≤ k := le_trans hK₀ hkK₀
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have hsplit : ((k : ℝ) ^ q)⁻¹ = ((k : ℝ) ^ (q - 2))⁻¹ * ((k : ℝ) ^ 2)⁻¹ := by
      have h : (k : ℝ) ^ q = (k : ℝ) ^ (q - 2) * (k : ℝ) ^ 2 := by
        rw [← pow_add]
        congr 1
        omega
      rw [h, mul_inv]
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right
      ((inv_le_inv₀ (by positivity) (by positivity)).mpr
        (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hkK₀) (q - 2)))
      (by positivity)
  have hIoo : Finset.Ico K₀ M = Finset.Ioo (K₀ - 1) M := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_Ioo]
    omega
  rw [hIoo]
  calc ∑ k ∈ Finset.Ioo (K₀ - 1) M, ((k : ℝ) ^ q)⁻¹
      ≤ ∑ k ∈ Finset.Ioo (K₀ - 1) M, ((K₀ : ℝ) ^ (q - 2))⁻¹ * ((k : ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum hpt
    _ = ((K₀ : ℝ) ^ (q - 2))⁻¹ * ∑ k ∈ Finset.Ioo (K₀ - 1) M, ((k : ℝ) ^ 2)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ ((K₀ : ℝ) ^ (q - 2))⁻¹ * (2 / (((K₀ - 1 : ℕ) : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le (α := ℝ) (K₀ - 1) M) (by positivity)
    _ = 2 * (((K₀ : ℝ) ^ (q - 1))⁻¹) := by
        have hKcast : (((K₀ - 1 : ℕ) : ℝ) + 1) = (K₀ : ℝ) := by
          exact_mod_cast (Nat.sub_add_cancel hK₀ : K₀ - 1 + 1 = K₀)
        have hq1 : q - 1 = (q - 2) + 1 := by omega
        rw [hKcast, hq1, pow_succ, mul_inv, div_eq_mul_inv]
        ring

end

end Work.BoseBoxFock.PCFU
