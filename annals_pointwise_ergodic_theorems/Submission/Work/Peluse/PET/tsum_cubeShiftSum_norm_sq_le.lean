import Mathlib
import Submission.Work.Peluse.Basic

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.PET

/-! ## Cauchy–Schwarz for a finite sum in `ℂ`

The elementary inequality `‖∑_{i ∈ s} f i‖² ≤ #s · ∑_{i ∈ s} ‖f i‖²`. -/
lemma norm_sum_sq_le_card_mul_sum_norm_sq {ι : Type*} (s : Finset ι) (F : ι → ℂ) :
    ‖∑ i ∈ s, F i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖F i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ s, F i‖ ≤ ∑ i ∈ s, ‖F i‖ := norm_sum_le _ _
  have h2 : ‖∑ i ∈ s, F i‖ ^ 2 ≤ (∑ i ∈ s, ‖F i‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : (∑ i ∈ s, ‖F i‖) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖F i‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  linarith

/-! ## The symmetric interval `[-N,N]` -/

/-- Membership in `symIcc N` expressed with the integer absolute value. -/
lemma mem_symIcc_iff_abs {N : ℕ} {x : ℤ} :
    x ∈ Work.Peluse.symIcc N ↔ |x| ≤ (N : ℤ) := by
  rw [Work.Peluse.symIcc, Finset.mem_Icc, abs_le]

/-- The cardinality of `[-N,N]`. -/
lemma card_symIcc (N : ℕ) : (Work.Peluse.symIcc N).card = 2 * N + 1 := by
  have h := Int.card_Icc_of_le (a := -(N : ℤ)) (b := (N : ℤ)) (by omega)
  have h2 : ((N : ℤ) + 1 - (-(N : ℤ))) = ((2 * N + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h2] at h
  exact_mod_cast h

/-- Cauchy–Schwarz for a `tsum` over `ℤ` whose summand is supported on a finite set. -/
lemma norm_tsum_sq_le_card_mul {f : ℤ → ℂ} {S : Finset ℤ}
    (hf : ∀ x : ℤ, x ∉ S → f x = 0) :
    ‖∑' x : ℤ, f x‖ ^ 2 ≤ (S.card : ℝ) * ∑' x : ℤ, ‖f x‖ ^ 2 := by
  rw [tsum_eq_sum hf, tsum_eq_sum (fun x hx => by rw [hf x hx]; simp)]
  exact norm_sum_sq_le_card_mul_sum_norm_sq S f

/-- **The key inequality, in the form where the corner shift is an abstract function.**

For a function `h` supported in `[-N,N]` and a family of cube shift sums
`x ↦ ∑_{a ∈ Q(last)} ∏_{τ} (star^[weight τ]) (h (x + a + c τ))`, the sum of the values is
controlled by twice the cardinality of the support of `h` times the sum of the squares of the
absolute values.  The point is that whenever the sum is nonzero there is an `a ∈ Q(last)` with all
the factors nonzero, hence with `x + a + c τ₀ ∈ [-N,N]`; since `|a| ≤ N` this forces
`x + c τ₀ ∈ [-2N,2N]`, so the whole sum is supported on the translate
`[-2N,2N] - c τ₀`, of cardinality `4N+1 ≤ 2·(2N+1) = 2·#[-N,N]`. -/
lemma cube_shift_tsum_sq_le {n : ℕ} (Q : Fin (n + 1) → Finset ℤ) {N : ℕ}
    (h : ℤ → ℂ) (hbd : ∀ a ∈ Q (Fin.last n), |a| ≤ (N : ℤ))
    (hsupp : ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → h x = 0)
    (c : (Fin n → Bool) → ℤ) (τ₀ : Fin n → Bool) :
    ‖∑' x : ℤ, ∑ a : {y : ℤ // y ∈ Q (Fin.last n)},
        ∏ τ : Fin n → Bool, (star^[Work.Peluse.weight τ]) (h (x + a.1 + c τ))‖ ^ 2
      ≤ 2 * ((Work.Peluse.symIcc N).card : ℝ) *
        ∑' x : ℤ, ‖∑ a : {y : ℤ // y ∈ Q (Fin.last n)},
          ∏ τ : Fin n → Bool, (star^[Work.Peluse.weight τ]) (h (x + a.1 + c τ))‖ ^ 2 := by
  classical
  set S : Finset ℤ := (Work.Peluse.symIcc (2 * N)).image (fun y : ℤ => y - c τ₀) with hS
  have hB : ∀ x : ℤ, x ∉ S →
      (∑ a : {y : ℤ // y ∈ Q (Fin.last n)},
        ∏ τ : Fin n → Bool, (star^[Work.Peluse.weight τ]) (h (x + a.1 + c τ))) = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
      (f := fun a : {y : ℤ // y ∈ Q (Fin.last n)} =>
        ∏ τ : Fin n → Bool, (star^[Work.Peluse.weight τ]) (h (x + a.1 + c τ))) hne
    have hfac : ∀ τ ∈ (Finset.univ : Finset (Fin n → Bool)),
        (star^[Work.Peluse.weight τ]) (h (x + a.1 + c τ)) ≠ 0 :=
      (Finset.prod_ne_zero_iff).mp ha
    have hτne : (star^[Work.Peluse.weight τ₀]) (h (x + a.1 + c τ₀)) ≠ 0 :=
      hfac τ₀ (Finset.mem_univ τ₀)
    have hh : h (x + a.1 + c τ₀) ≠ 0 := by
      intro hz
      exact hτne (by rw [hz]; simp)
    have hmem : x + a.1 + c τ₀ ∈ Work.Peluse.symIcc N := by
      by_contra hnot
      exact hh (hsupp _ hnot)
    rw [Work.Peluse.symIcc, Finset.mem_Icc] at hmem
    have h1 : |x + a.1 + c τ₀| ≤ (N : ℤ) := abs_le.mpr hmem
    have h2 : |a.1| ≤ (N : ℤ) := hbd a.1 a.2
    have habs : |x + c τ₀| ≤ ((2 * N : ℕ) : ℤ) := by
      have hsplit : x + c τ₀ = (x + a.1 + c τ₀) - a.1 := by ring
      rw [hsplit]
      refine le_trans (abs_sub _ _) ?_
      have hcast : (N : ℤ) + (N : ℤ) = ((2 * N : ℕ) : ℤ) := by push_cast; ring
      linarith
    refine hx ?_
    rw [hS]
    refine Finset.mem_image.mpr ⟨x + c τ₀, ?_, by ring⟩
    rw [Work.Peluse.symIcc, Finset.mem_Icc]
    exact abs_le.mp habs
  have hmain : ‖∑' x : ℤ, (∑ a : {y : ℤ // y ∈ Q (Fin.last n)},
        ∏ τ : Fin n → Bool, (star^[Work.Peluse.weight τ]) (h (x + a.1 + c τ)))‖ ^ 2
      ≤ (S.card : ℝ) * ∑' x : ℤ, ‖(∑ a : {y : ℤ // y ∈ Q (Fin.last n)},
        ∏ τ : Fin n → Bool, (star^[Work.Peluse.weight τ]) (h (x + a.1 + c τ)))‖ ^ 2 :=
    norm_tsum_sq_le_card_mul hB
  have hcard : (S.card : ℝ) ≤ 2 * ((Work.Peluse.symIcc N).card : ℝ) := by
    have h0 : S.card ≤ 2 * (Work.Peluse.symIcc N).card := by
      have h00 : S.card ≤ (Work.Peluse.symIcc (2 * N)).card := by
        rw [hS]; exact Finset.card_image_le
      rw [card_symIcc (2 * N)] at h00
      rw [card_symIcc N]
      omega
    exact_mod_cast h0
  have hnn : 0 ≤ ∑' x : ℤ, ‖(∑ a : {y : ℤ // y ∈ Q (Fin.last n)},
      ∏ τ : Fin n → Bool, (star^[Work.Peluse.weight τ]) (h (x + a.1 + c τ)))‖ ^ 2 :=
    tsum_nonneg (fun _ => by positivity)
  calc ‖∑' x : ℤ, (∑ a : {y : ℤ // y ∈ Q (Fin.last n)},
        ∏ τ : Fin n → Bool, (star^[Work.Peluse.weight τ]) (h (x + a.1 + c τ)))‖ ^ 2
      ≤ (S.card : ℝ) * ∑' x : ℤ, ‖(∑ a : {y : ℤ // y ∈ Q (Fin.last n)},
        ∏ τ : Fin n → Bool, (star^[Work.Peluse.weight τ]) (h (x + a.1 + c τ)))‖ ^ 2 := hmain
    _ ≤ 2 * ((Work.Peluse.symIcc N).card : ℝ) * ∑' x : ℤ, ‖(∑ a : {y : ℤ // y ∈ Q (Fin.last n)},
        ∏ τ : Fin n → Bool, (star^[Work.Peluse.weight τ]) (h (x + a.1 + c τ)))‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hcard hnn

theorem tsum_cubeShiftSum_norm_sq_le {n : ℕ} (Q : Fin (n + 1) → Finset ℤ) {N : ℕ} (hN : 0 < N)
    (h : ℤ → ℂ) (hbd : ∀ a ∈ Q (Fin.last n), |a| ≤ (N : ℤ))
    (hsupp : ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → h x = 0)
    (z z' : (i : Fin n) → {x : ℤ // x ∈ Q i.castSucc}) :
    ‖∑' x : ℤ, ∑ a : {x : ℤ // x ∈ Q (Fin.last n)},
        ∏ τ : Fin n → Bool, (star^[Work.Peluse.weight τ])
          (h (x + a.1 + Work.Peluse.cornerShift (fun i => (z i).1) (fun i => (z' i).1) τ))‖ ^ 2
      ≤ 2 * ((Work.Peluse.symIcc N).card : ℝ) *
        ∑' x : ℤ, ‖∑ a : {x : ℤ // x ∈ Q (Fin.last n)},
          ∏ τ : Fin n → Bool, (star^[Work.Peluse.weight τ])
            (h (x + a.1 + Work.Peluse.cornerShift (fun i => (z i).1) (fun i => (z' i).1) τ))‖ ^ 2 := by
  classical
  have _hN : 0 < N := hN
  exact cube_shift_tsum_sq_le Q h hbd hsupp
    (fun τ => Work.Peluse.cornerShift (fun i => (z i).1) (fun i => (z' i).1) τ)
    (fun _ => false)

end Work.Peluse.PET
