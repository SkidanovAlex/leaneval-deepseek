import Submission.Grassmann.SpectralSSE
import Submission.Grassmann.SmallInfl
import Submission.Grassmann.EOp

/-!
# `cor:atmostd`: the Bonami-type inequality for global functions on `L(V,W)`

This file derives **`HypBSglob`** (the paper's `cor:atmostd`, Corollary 1.4 of
arXiv:2209.04243) from the *corollary of hypercontractivity* `HypCor4`.

The argument is the one described in the ROADMAP:

1. the degree-`d` truncation is the sum of its pure levels, `truncBS d f = Σ_{i ≤ d} f^{=i}`;
2. consequently the derivative of the truncation splits as
   `D_{V₁,W₁,T}[f^{≤d}] = Σ_{i ≤ d} D_{V₁,W₁,T}[f^{=i}]`;
3. Cauchy–Schwarz over the `d+1` terms (`l2sq_sum_le`) bounds the squared `L²` norm of the
   derivative by `(d+1) Σ_{i≤d} I_{V₁,W₁,T}[f^{=i}]`;
4. each `I_{V₁,W₁,T}[f^{=i}] ≤ C i · ε` by Proposition 5.6 (`prop_5_6`) applied at level `i`,
   together with the vanishing of the hybrid Laplacian for orders exceeding `i`
   (`SmallInfl_of_le_order_nprojPure`);
5. hence `f^{≤d}` has `(d, (d+1)² C d ε)`-small generalised influences and `HypCor4` applies,
   with the additive constant `15` absorbed into `2^{C d²}`.

Unlike the paper's `cor:atmostd` no Boolean-ness hypothesis is needed: once the influence of
the truncation is bounded, `HypCor4` (which is itself the Boolean-free corollary of
hypercontractivity) applies directly.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

/-! ## The level decomposition of the truncation -/

/-- **The degree-`d` truncation is the sum of its pure levels.** -/
lemma truncBS_eq_sum_nprojPure {m n : ℕ} (d : ℕ)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    truncBS d f = ∑ i ∈ Finset.range (d + 1), nprojPure i f := by
  funext A
  simp only [truncBS, lapMulN, lapMul, nprojPure, projPure, Pi.smul_apply, Finset.sum_apply,
    smul_eq_mul]
  rw [← Finset.mul_sum]
  congr 1
  refine (Finset.sum_congr rfl (fun X (_ : X ∈ Finset.univ) => ?_)).trans Finset.sum_comm
  by_cases h : X.rank ≤ d
  · rw [if_pos h]
    exact ((Finset.sum_eq_single X.rank (fun b _ hb => if_neg (fun hc => hb hc.symm))
      (fun hmem => absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le h)) hmem)).trans
        (if_pos rfl)).symm
  · rw [if_neg h]
    exact ((Finset.sum_eq_zero (fun i hi => by
      rw [if_neg]
      intro hc
      have := Finset.mem_range.mp hi
      omega)).symm)

/-! ## The derivative of a sum -/

/-- The shift is additive over finite sums. -/
lemma shift_sum {m n : ℕ} {ι : Type*} (T : Matrix (Fin m) (Fin n) 𝔽₂) (s : Finset ι)
    (g : ι → Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    shift T (∑ i ∈ s, g i) = ∑ i ∈ s, shift T (g i) := by
  funext A
  simp only [shift, Finset.sum_apply]

/-- The restricted shifted derivative is additive over finite sums. -/
lemma restr_shift_sum {m n m' n' : ℕ} {ι : Type*} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (inj : Matrix (Fin m) (Fin m') 𝔽₂) (T : Matrix (Fin m) (Fin n) 𝔽₂) (s : Finset ι)
    (g : ι → Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    restr Q inj (shift T (∑ i ∈ s, g i)) = ∑ i ∈ s, restr Q inj (shift T (g i)) := by
  rw [shift_sum, restr_sum]

/-! ## The constant `C` is monotone -/

lemma C_mono {i d : ℕ} (h : i ≤ d) : C i ≤ C d := by
  rw [C, C]
  refine mul_le_mul (pow_le_pow_right₀ (by norm_num) h) ?_ (by positivity) (by positivity)
  exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul (by omega) (by omega))

/-! ## Small influences of the truncation -/

/-- **The truncation has small generalised influences.**  If `f` is `(d,ε)`-restriction global
then `f^{≤d}` has `(d, (d+1)² C d ε)`-small generalised influences. -/
theorem smallInfl_truncBS {m n d : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hglob : GlobalBS d ε f) :
    SmallInfl d (((d : ℝ) + 1) * (((d : ℝ) + 1) * (C d * ε))) (truncBS d f) := by
  intro m' n' Q ι T hord
  simp only [inflBS2]
  have hdec : lapMulN (hybridPred Q ι) (truncBS d f) =
      ∑ i ∈ Finset.range (d + 1), lapMulN (hybridPred Q ι) (nprojPure i f) := by
    rw [truncBS_eq_sum_nprojPure, lapMulN_sum]
  have hsum : restr Q ι (shift T (lapMulN (hybridPred Q ι) (truncBS d f))) =
      ∑ i ∈ Finset.range (d + 1),
        restr Q ι (shift T (lapMulN (hybridPred Q ι) (nprojPure i f))) := by
    rw [hdec, restr_shift_sum]
  rw [hsum]
  have hfun : (∑ i ∈ Finset.range (d + 1),
        restr Q ι (shift T (lapMulN (hybridPred Q ι) (nprojPure i f)))) =
      fun A => ∑ i ∈ Finset.range (d + 1),
        (restr Q ι (shift T (lapMulN (hybridPred Q ι) (nprojPure i f)))) A := by
    funext A; rw [Finset.sum_apply]
  rw [hfun]
  refine (l2sq_sum_le (Finset.range (d + 1))
    (fun i => restr Q ι (shift T (lapMulN (hybridPred Q ι) (nprojPure i f))))).trans ?_
  have hterm : ∀ i ∈ Finset.range (d + 1),
      l2sq (restr Q ι (shift T (lapMulN (hybridPred Q ι) (nprojPure i f)))) ≤ C i * ε := by
    intro i hi
    have hid : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hglobi : GlobalBS i ε f := GlobalBS_mono hid hglob
    have hprop : SmallInfl i (C i * ε) (nprojPure i f) := prop_5_6 i ε hε m n f hglobi
    have hCi : 0 ≤ C i * ε := mul_nonneg (le_trans zero_le_one (one_le_C i)) hε
    exact SmallInfl_of_le_order_nprojPure hid hCi hprop Q ι T hord
  have hb : (∑ i ∈ Finset.range (d + 1),
        l2sq (restr Q ι (shift T (lapMulN (hybridPred Q ι) (nprojPure i f)))))
      ≤ (∑ _i ∈ Finset.range (d + 1), C d * ε) := by
    refine Finset.sum_le_sum fun i hi => ?_
    exact (hterm i hi).trans (mul_le_mul_of_nonneg_right
      (C_mono (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))) hε)
  have hconst : (∑ _i ∈ Finset.range (d + 1), C d * ε) = ((d : ℝ) + 1) * (C d * ε) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  rw [Finset.card_range, Nat.cast_add, Nat.cast_one]
  calc ((d : ℝ) + 1) * (∑ i ∈ Finset.range (d + 1),
        l2sq (restr Q ι (shift T (lapMulN (hybridPred Q ι) (nprojPure i f)))))
      ≤ ((d : ℝ) + 1) * (∑ _i ∈ Finset.range (d + 1), C d * ε) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = ((d : ℝ) + 1) * (((d : ℝ) + 1) * (C d * ε)) := by rw [hconst]

/-! ## The arithmetic bound -/

/-- The factor `(d+1)² C d` is absorbed by `2^{15 d²}`. -/
lemma d_plus_one_sq_mul_C_le (d : ℕ) :
    ((d : ℝ) + 1) ^ 2 * C d ≤ (2 : ℝ) ^ (15 * d ^ 2) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    norm_num [C]
  · have hnat : d + 1 ≤ 2 ^ (d + 1) := Nat.le_of_lt (Nat.lt_two_pow_self (n := d + 1))
    have hreal : ((d : ℝ) + 1) ≤ (2 : ℝ) ^ (d + 1) := by
      have hcast : (((d + 1 : ℕ) : ℝ)) ≤ (((2 ^ (d + 1) : ℕ)) : ℝ) := by exact_mod_cast hnat
      simpa using hcast
    have h1 : ((d : ℝ) + 1) ^ 2 ≤ (2 : ℝ) ^ (2 * d + 2) := by
      calc ((d : ℝ) + 1) ^ 2 ≤ ((2 : ℝ) ^ (d + 1)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hreal 2
        _ = (2 : ℝ) ^ (2 * d + 2) := by
            rw [← pow_mul]
            congr 1
            ring
    have h2 : C d ≤ (2 : ℝ) ^ (2 * d ^ 2 + 9 * d) := C_le d
    have h3 : (2 : ℝ) ^ (2 * d + 2) * (2 : ℝ) ^ (2 * d ^ 2 + 9 * d) =
        (2 : ℝ) ^ (2 * d ^ 2 + 11 * d + 2) := by
      rw [← pow_add]
      congr 1
      ring
    have h4 : 2 * d ^ 2 + 11 * d + 2 ≤ 15 * d ^ 2 := by nlinarith [hd]
    calc ((d : ℝ) + 1) ^ 2 * C d
        ≤ (2 : ℝ) ^ (2 * d + 2) * (2 : ℝ) ^ (2 * d ^ 2 + 9 * d) :=
          mul_le_mul h1 h2 (le_trans zero_le_one (one_le_C d)) (by positivity)
      _ = (2 : ℝ) ^ (2 * d ^ 2 + 11 * d + 2) := h3
      _ ≤ (2 : ℝ) ^ (15 * d ^ 2) := pow_le_pow_right₀ (by norm_num) h4

/-! ## The main theorem -/

/-- **`cor:atmostd` from the corollary of hypercontractivity.** -/
theorem HypBSglob_of_HypCor4 (H : HypCor4) : HypBSglob := by
  obtain ⟨K, hK, hcor⟩ := H
  refine ⟨((K + 15 : ℕ) : ℝ), by positivity, ?_⟩
  intro m n d f ε hε _hbool hglob
  set ε' : ℝ := ((d : ℝ) + 1) * (((d : ℝ) + 1) * (C d * ε)) with hε'def
  have hε' : 0 ≤ ε' := by
    rw [hε'def]
    have h1 : (1 : ℝ) ≤ (d : ℝ) + 1 := by
      have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      linarith
    have h2 : 0 ≤ C d * ε := mul_nonneg (le_trans zero_le_one (one_le_C d)) hε
    exact mul_nonneg (by linarith) (mul_nonneg (by linarith) h2)
  have hSI : SmallInfl d ε' (truncBS d f) := by
    rw [hε'def]; exact smallInfl_truncBS hε hglob
  have h4 := hcor m n d (truncBS d f) ε' hε' (truncBS_degLe d f) hSI
  have hbound : (2 : ℝ) ^ (K * d ^ 2) * ε' ≤ (2 : ℝ) ^ ((K + 15) * d ^ 2) * ε := by
    have hkey : ((d : ℝ) + 1) ^ 2 * C d ≤ (2 : ℝ) ^ (15 * d ^ 2) := d_plus_one_sq_mul_C_le d
    have hfac : ε' = ((d : ℝ) + 1) ^ 2 * C d * ε := by
      rw [hε'def]; ring
    calc (2 : ℝ) ^ (K * d ^ 2) * ε'
        = (2 : ℝ) ^ (K * d ^ 2) * (((d : ℝ) + 1) ^ 2 * C d) * ε := by rw [hfac]; ring
      _ ≤ (2 : ℝ) ^ (K * d ^ 2) * (2 : ℝ) ^ (15 * d ^ 2) * ε := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkey (by positivity)) hε
      _ = (2 : ℝ) ^ (K * d ^ 2 + 15 * d ^ 2) * ε := by rw [pow_add]
      _ = (2 : ℝ) ^ ((K + 15) * d ^ 2) * ε := by
          congr 2
          ring
  calc l4q (truncBS d f)
      ≤ (2 : ℝ) ^ (K * d ^ 2) * ε' * l2sq (truncBS d f) := h4
    _ ≤ (2 : ℝ) ^ ((K + 15) * d ^ 2) * ε * l2sq (truncBS d f) :=
        mul_le_mul_of_nonneg_right hbound (l2sq_nonneg _)
    _ = (2 : ℝ) ^ (((K + 15 : ℕ) : ℝ) * (d : ℝ) ^ 2) * ε * l2sq (truncBS d f) := by
        rw [show (((K + 15 : ℕ) : ℝ) * (d : ℝ) ^ 2) = (((K + 15) * d ^ 2 : ℕ) : ℝ) by
          push_cast; ring]
        rw [Real.rpow_natCast]

end

end Submission.Grassmann
