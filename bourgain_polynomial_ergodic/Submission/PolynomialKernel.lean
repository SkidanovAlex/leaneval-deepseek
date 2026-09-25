/-
# The polynomial density kernel

For an integer polynomial `P` and an integer `N ≥ 1`, Bourgain's proof of the
polynomial ergodic theorem is driven by the *density kernel* of the sequence
`P(0), P(1), …, P(N-1)`,

  `k_N(j) = (1/N) · #{i < N : P(i) = j}`,

which satisfies `∑_j k_N(j) · f (T^[j] x) = (1/N) ∑_{i<N} f (T^[P(i)] x)`.

This file collects the elementary combinatorial facts about `k_N` that the
Calderón transference step consumes: a support bound `k_N(j) = 0` for
`j ≥ polySupport P N`, the identification with the ergodic average, and the
normalisation `∑_j |k_N(j)| ≤ 1`.
-/
import ChallengeDeps

open Finset
open scoped BigOperators

namespace Submission

/-- Counting fibres of a map into `ℕ`: summing the fibre cardinalities against `h`
reproduces the sum of `h ∘ a`. -/
theorem sum_fiber_card_mul {α : Type*} (s : Finset α) (a : α → ℕ) (J : ℕ)
    (hJ : ∀ i ∈ s, a i < J) (h : ℕ → ℝ) :
    (∑ j ∈ Finset.range J, ((s.filter (fun i => a i = j)).card : ℝ) * h j)
      = ∑ i ∈ s, h (a i) := by
  have hfib := Finset.sum_fiberwise_of_maps_to (s := s) (t := Finset.range J) (g := a)
    (fun i hi => Finset.mem_range.mpr (hJ i hi)) (fun i => h (a i))
  rw [← hfib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2])]
  rw [Finset.sum_const, nsmul_eq_mul]

/-- The polynomial density kernel `k_N(j) = (1/N) · #{i < N : P(i) = j}`, where
`P(i)` is read as the natural number `(P.eval i).toNat`. -/
noncomputable def polyKernel (P : Polynomial ℤ) (N j : ℕ) : ℝ :=
  (N : ℝ)⁻¹ *
    (((Finset.range N).filter (fun i : ℕ => (P.eval (i : ℤ)).toNat = j)).card : ℝ)

/-- A support bound for the polynomial density kernel: every value `P(i)`, `i < N`,
is strictly below `polySupport P N`. -/
noncomputable def polySupport (P : Polynomial ℤ) (N : ℕ) : ℕ :=
  ((Finset.range N).image (fun i : ℕ => (P.eval (i : ℤ)).toNat)).sup id + 1

theorem polySupport_spec (P : Polynomial ℤ) (N i : ℕ) (hi : i ∈ Finset.range N) :
    (P.eval (i : ℤ)).toNat < polySupport P N := by
  unfold polySupport
  have hmem : (P.eval (i : ℤ)).toNat ∈
      (Finset.range N).image (fun i : ℕ => (P.eval (i : ℤ)).toNat) :=
    Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have h := Finset.le_sup (f := id) hmem
  simp only [id_eq] at h
  omega

/-- The defining property of the density kernel: summing `g` against the number of
preimages of `j` reproduces the sum of `g ∘ P`. -/
theorem sum_card_filter_mul (P : Polynomial ℤ) (N : ℕ) (g : ℕ → ℝ) :
    (∑ j ∈ Finset.range (polySupport P N),
        (((Finset.range N).filter (fun i : ℕ => (P.eval (i : ℤ)).toNat = j)).card : ℝ)
          * g j)
      = ∑ i ∈ Finset.range N, g ((P.eval (i : ℤ)).toNat) :=
  sum_fiber_card_mul (Finset.range N) (fun i : ℕ => (P.eval (i : ℤ)).toNat)
    (polySupport P N) (fun i hi => polySupport_spec P N i hi) g

/-- The density kernel reproduces the polynomial ergodic average. -/
theorem sum_polyKernel_mul_orbit {X : Type*} (P : Polynomial ℤ) (N : ℕ) (f : X → ℝ)
    (T : X → X) (x : X) :
    (∑ j ∈ Finset.range (polySupport P N), polyKernel P N j * f (T^[j] x))
      = (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, f (T^[(P.eval (i : ℤ)).toNat] x) := by
  rw [show (∑ j ∈ Finset.range (polySupport P N), polyKernel P N j * f (T^[j] x))
      = ∑ j ∈ Finset.range (polySupport P N),
          (N : ℝ)⁻¹ * (((((Finset.range N).filter
            (fun i : ℕ => (P.eval (i : ℤ)).toNat = j)).card : ℕ) : ℝ) * f (T^[j] x)) from
      Finset.sum_congr rfl (fun j _ => by unfold polyKernel; ring)]
  rw [← Finset.mul_sum]
  rw [sum_card_filter_mul]

/-- The density kernel is supported in `[0, polySupport P N)`. -/
theorem polyKernel_eq_zero_of_support (P : Polynomial ℤ) (N j : ℕ)
    (hj : polySupport P N ≤ j) : polyKernel P N j = 0 := by
  unfold polyKernel
  have hempty : (Finset.range N).filter (fun i : ℕ => (P.eval (i : ℤ)).toNat = j) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    rw [Finset.mem_filter] at hi
    have := polySupport_spec P N i hi.1
    omega
  rw [hempty]
  simp

/-- Normalisation of the density kernel: `∑_j |k_N(j)| ≤ 1`. -/
theorem sum_abs_polyKernel_le_one (P : Polynomial ℤ) (N : ℕ) :
    ∑ j ∈ Finset.range (polySupport P N), |polyKernel P N j| ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have hps : polySupport P 0 = 1 := by simp [polySupport]
    rw [hps, Finset.sum_range_one]
    simp [polyKernel]
  · have hcast : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hnonneg : ∀ j, 0 ≤ polyKernel P N j := fun j => by unfold polyKernel; positivity
    have hsum : ∑ j ∈ Finset.range (polySupport P N), polyKernel P N j = 1 := by
      have h := sum_card_filter_mul P N (fun _ : ℕ => (1 : ℝ))
      simp only [mul_one] at h
      rw [show (∑ j ∈ Finset.range (polySupport P N), polyKernel P N j)
          = (N : ℝ)⁻¹ * ∑ j ∈ Finset.range (polySupport P N),
              (((Finset.range N).filter
                (fun i : ℕ => (P.eval (i : ℤ)).toNat = j)).card : ℝ) from by
        unfold polyKernel
        rw [Finset.mul_sum]]
      rw [h]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      field_simp
    rw [Finset.sum_congr rfl (fun j _ => abs_of_nonneg (hnonneg j)), hsum]

end Submission
