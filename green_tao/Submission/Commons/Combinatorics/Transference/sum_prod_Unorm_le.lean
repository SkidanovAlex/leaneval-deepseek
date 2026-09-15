import Mathlib
import Submission.Commons.Combinatorics.Transference.Unorm_pow
import Submission.Commons.Combinatorics.Transference.Unorm_nonneg
import Submission.Commons.Analysis.Convex.prod_le_inv_card_mul_sum_pow
import Submission.Commons.Analysis.Order.pow_le_one_add_pow

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- AM–GM plus the elementary power comparison: if `x` is nonnegative on `s` and
`s.card ≤ n` then `∏_{i∈s} x i ≤ 1 + |s|⁻¹ ∑_{i∈s} x i ^ n`. -/
theorem prod_le_one_add_inv_card_mul_sum_pow {ι : Type*} (s : Finset ι) {n : ℕ}
    (hs : s.Nonempty) (hn : s.card ≤ n) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) :
    ∏ i ∈ s, x i ≤ 1 + (s.card : ℝ)⁻¹ * ∑ i ∈ s, x i ^ n := by
  have hcard : (s.card : ℝ) ≠ 0 := by
    have : 0 < s.card := Finset.card_pos.mpr hs
    exact_mod_cast this.ne'
  have h1 := Commons.Analysis.Convex.prod_le_inv_card_mul_sum_pow s x hs hx
  have h2 : ∑ i ∈ s, x i ^ s.card ≤ ∑ i ∈ s, x i ^ n + (s.card : ℝ) := by
    have h2' : ∑ i ∈ s, x i ^ s.card ≤ ∑ i ∈ s, (1 + x i ^ n) :=
      Finset.sum_le_sum fun i hi => Commons.Analysis.Order.pow_le_one_add_pow (hx i hi) hn
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at h2'
    linarith
  calc ∏ i ∈ s, x i
      ≤ (s.card : ℝ)⁻¹ * ∑ i ∈ s, x i ^ s.card := h1
    _ ≤ (s.card : ℝ)⁻¹ * (∑ i ∈ s, x i ^ n + (s.card : ℝ)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 1 + (s.card : ℝ)⁻¹ * ∑ i ∈ s, x i ^ n := by
        rw [mul_add, inv_mul_cancel₀ hcard]; ring

/-- `Fin K → Fin d → G` has `|G|^{dK}` elements. -/
theorem card_fun_fun_fin {G : Type*} [Fintype G] (d K : ℕ) :
    Fintype.card (Fin K → Fin d → G) = (Fintype.card G) ^ (d * K) := by
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_mul]

/-- **AM–GM step of the polynomial lemma.**  If for every nonzero cube vertex `ω` the
normalised `H`-average of the cube sum of `g_{ω·H}(x) = ∏_j F_j (x + ω·H_j)` is bounded by
`Bm`, then the sum over `H` of the product of the `U^d` norms of the `g_{ω·H}` is bounded
by `|G|^{dK}(1 + Bm)`. -/
theorem sum_prod_Unorm_le {G : Type*} [AddCommGroup G] [Fintype G] (d : ℕ) (hd : 1 ≤ d)
    {K : ℕ} (F : Fin K → G → ℝ) {Bm : ℝ}
    (hB : ∀ ω : Fin d → Bool, ω ≠ 0 →
      ((Fintype.card G : ℝ) ^ (d * K))⁻¹ * ((Fintype.card G : ℝ) ^ (d+1))⁻¹ *
        (∑ H : Fin K → Fin d → G, ∑ h : Fin d → G, ∑ x : G,
          ∏ ω' : Fin d → Bool, ∏ j : Fin K,
            F j (x + (∑ i, if ω' i then h i else 0) + (∑ i, if ω i then H j i else 0))) ≤ Bm) :
    ∑ H : Fin K → Fin d → G, ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)),
        Unorm d (fun x => ∏ j : Fin K, F j (x + ∑ i, if ω i then H j i else 0))
      ≤ ((Fintype.card G : ℝ) ^ (d * K)) * (1 + Bm) := by
  classical
  have hNpos : (0 : ℝ) < (Fintype.card G : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(0 : G)⟩ : 0 < Fintype.card G)
  have hNne : (Fintype.card G : ℝ) ≠ 0 := ne_of_gt hNpos
  let s : Finset (Fin d → Bool) := Finset.univ.erase (0 : Fin d → Bool)
  let g : (Fin K → Fin d → G) → (Fin d → Bool) → G → ℝ :=
    fun H ω x => ∏ j : Fin K, F j (x + ∑ i, if ω i then H j i else 0)
  change ∑ H : Fin K → Fin d → G, ∏ ω ∈ s, Unorm d (g H ω)
      ≤ ((Fintype.card G : ℝ) ^ (d * K)) * (1 + Bm)
  have hsne : s.Nonempty := by
    refine ⟨fun _ => true, ?_⟩
    show (fun _ : Fin d => true) ∈ Finset.univ.erase (0 : Fin d → Bool)
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro h
    have := congrFun h ⟨0, hd⟩
    simp at this
  have hscard_le : s.card ≤ 2 ^ d := by
    calc s.card ≤ Fintype.card (Fin d → Bool) := Finset.card_le_univ s
      _ = 2 ^ d := by rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  have hscardne : (s.card : ℝ) ≠ 0 := by
    have : 0 < s.card := Finset.card_pos.mpr hsne
    exact_mod_cast this.ne'
  -- Step A: pointwise AM–GM bound
  have hA : ∀ H : Fin K → Fin d → G,
      ∏ ω ∈ s, Unorm d (g H ω) ≤
        1 + (s.card : ℝ)⁻¹ * ∑ ω ∈ s, cubeSum d (g H ω) / (Fintype.card G : ℝ) ^ (d + 1) := by
    intro H
    have hb : ∀ ω ∈ s, 0 ≤ Unorm d (g H ω) := fun ω _ => Unorm_nonneg d hd _
    have h1 := Commons.Analysis.Convex.prod_le_inv_card_mul_sum_pow s
      (fun ω => Unorm d (g H ω)) hsne hb
    have h2 : ∑ ω ∈ s, (Unorm d (g H ω)) ^ s.card ≤
        ∑ ω ∈ s, (Unorm d (g H ω)) ^ (2 ^ d) + (s.card : ℝ) := by
      have h2' : ∑ ω ∈ s, (Unorm d (g H ω)) ^ s.card ≤
          ∑ ω ∈ s, (1 + (Unorm d (g H ω)) ^ (2 ^ d)) :=
        Finset.sum_le_sum fun ω hω =>
          Commons.Analysis.Order.pow_le_one_add_pow (hb ω hω) hscard_le
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at h2'
      linarith
    calc ∏ ω ∈ s, Unorm d (g H ω)
        ≤ (s.card : ℝ)⁻¹ * ∑ ω ∈ s, (Unorm d (g H ω)) ^ s.card := h1
      _ ≤ (s.card : ℝ)⁻¹ * (∑ ω ∈ s, (Unorm d (g H ω)) ^ (2 ^ d) + (s.card : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 1 + (s.card : ℝ)⁻¹ * ∑ ω ∈ s, (Unorm d (g H ω)) ^ (2 ^ d) := by
          rw [mul_add, inv_mul_cancel₀ hscardne]; ring
      _ = 1 + (s.card : ℝ)⁻¹ *
            ∑ ω ∈ s, cubeSum d (g H ω) / (Fintype.card G : ℝ) ^ (d + 1) := by
          rw [Finset.sum_congr rfl (fun ω _ => Unorm_pow d hd (g H ω))]
  -- Step B: the hypothesis, normalised
  have hBstep : ∀ ω ∈ s,
      ∑ H : Fin K → Fin d → G, cubeSum d (g H ω) / (Fintype.card G : ℝ) ^ (d + 1)
        ≤ ((Fintype.card G : ℝ) ^ (d * K)) * Bm := by
    intro ω hω
    have hmem : ω ∈ Finset.univ.erase (0 : Fin d → Bool) := by simpa only [s] using hω
    have hω0 : ω ≠ 0 := (Finset.mem_erase.mp hmem).1
    have hh := hB ω hω0
    have hh' : ((Fintype.card G : ℝ) ^ (d * K))⁻¹ * ((Fintype.card G : ℝ) ^ (d + 1))⁻¹ *
        (∑ H : Fin K → Fin d → G, cubeSum d (g H ω)) ≤ Bm := by
      simpa only [cubeSum, g] using hh
    have hN2 : ((Fintype.card G : ℝ) ^ (d * K)) ≠ 0 := pow_ne_zero _ hNne
    have hkey : ((Fintype.card G : ℝ) ^ (d * K))⁻¹ *
        ∑ H : Fin K → Fin d → G, cubeSum d (g H ω) / (Fintype.card G : ℝ) ^ (d + 1)
          ≤ Bm := by
      have heq : ((Fintype.card G : ℝ) ^ (d * K))⁻¹ *
            ∑ H : Fin K → Fin d → G, cubeSum d (g H ω) / (Fintype.card G : ℝ) ^ (d + 1)
          = ((Fintype.card G : ℝ) ^ (d * K))⁻¹ * ((Fintype.card G : ℝ) ^ (d + 1))⁻¹ *
            (∑ H : Fin K → Fin d → G, cubeSum d (g H ω)) := by
        simp only [div_eq_mul_inv]
        rw [← Finset.sum_mul]
        ring
      rw [heq]; exact hh'
    calc ∑ H : Fin K → Fin d → G, cubeSum d (g H ω) / (Fintype.card G : ℝ) ^ (d + 1)
        = ((Fintype.card G : ℝ) ^ (d * K)) *
            (((Fintype.card G : ℝ) ^ (d * K))⁻¹ *
              ∑ H : Fin K → Fin d → G, cubeSum d (g H ω) / (Fintype.card G : ℝ) ^ (d + 1)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hN2, one_mul]
      _ ≤ ((Fintype.card G : ℝ) ^ (d * K)) * Bm :=
          mul_le_mul_of_nonneg_left hkey (pow_nonneg hNpos.le _)
  -- Assembly
  have hcardHK : (Fintype.card (Fin K → Fin d → G) : ℝ) = (Fintype.card G : ℝ) ^ (d * K) := by
    rw [card_fun_fun_fin]; push_cast; ring
  calc ∑ H : Fin K → Fin d → G, ∏ ω ∈ s, Unorm d (g H ω)
      ≤ ∑ H : Fin K → Fin d → G,
          (1 + (s.card : ℝ)⁻¹ *
            ∑ ω ∈ s, cubeSum d (g H ω) / (Fintype.card G : ℝ) ^ (d + 1)) :=
        Finset.sum_le_sum fun H _ => hA H
    _ = (Fintype.card (Fin K → Fin d → G) : ℝ) +
          (s.card : ℝ)⁻¹ * ∑ ω ∈ s,
            ∑ H : Fin K → Fin d → G, cubeSum d (g H ω) / (Fintype.card G : ℝ) ^ (d + 1) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm, Finset.sum_const,
          nsmul_eq_mul, mul_one, Finset.card_univ]
    _ ≤ (Fintype.card G : ℝ) ^ (d * K) +
          (s.card : ℝ)⁻¹ *
            ((s.card : ℝ) * (((Fintype.card G : ℝ) ^ (d * K)) * Bm)) := by
        rw [hcardHK]
        refine add_le_add_right ?_ _
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ∑ ω ∈ s, ∑ H : Fin K → Fin d → G,
                cubeSum d (g H ω) / (Fintype.card G : ℝ) ^ (d + 1)
            ≤ ∑ ω ∈ s, ((Fintype.card G : ℝ) ^ (d * K)) * Bm :=
              Finset.sum_le_sum fun ω hω => hBstep ω hω
          _ = (s.card : ℝ) * (((Fintype.card G : ℝ) ^ (d * K)) * Bm) := by
              rw [Finset.sum_const, nsmul_eq_mul]
    _ = (Fintype.card G : ℝ) ^ (d * K) * (1 + Bm) := by
        rw [← mul_assoc, inv_mul_cancel₀ hscardne, one_mul]; ring

end Commons.Combinatorics.Transference
