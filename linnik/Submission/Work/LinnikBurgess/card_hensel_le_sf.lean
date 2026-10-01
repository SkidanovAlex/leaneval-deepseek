import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs
import Submission.Work.LinnikBurgess.aeval_dist_eq_norm
import Submission.Work.LinnikBurgess.eq_of_dvd_sub_of_lt

/-!
# Hensel root count (Lemma H, U5): a fresh, `sorry`-free proof

`henselSet p P M` is the set of `y < p^M` for which `ν := v_p(P'(y))` is finite and
`p^(max (2ν+1) (M+ν)) ∣ P(y)`.  Its cardinality is at most `P.natDegree`.

The argument: each `y ∈ henselSet` is a point at which `P` is Hensel-approximable; Hensel's
lemma produces a root `z_y` of `P` in `ℤ_[p]` with `‖z_y - y‖ ≤ p^{-M}`.  Two distinct
`y, y' < p^M` give distinct roots, since otherwise `p^M ∣ y - y'`.  A nonzero polynomial of
degree `n` over the domain `ℤ_[p]` has at most `n` roots, whence the bound.
-/

open Polynomial

namespace Work.LinnikBurgess

section Aux

variable {p : ℕ} [Fact p.Prime]

/-- `eval`, at the image of an integer, of the reduction of an integral polynomial to `ℤ_[p]`. -/
lemma hensel_sf_eval_map_int (P : Polynomial ℤ) (y : ℤ) :
    (P.map (algebraMap ℤ ℤ_[p])).eval ((y : ℤ_[p])) = ((P.eval y : ℤ) : ℤ_[p]) := by
  rw [Polynomial.eval_map]
  rw [show ((y : ℤ_[p])) = (Int.castRingHom ℤ_[p]) y from rfl]
  rw [show (algebraMap ℤ ℤ_[p]) = (Int.castRingHom ℤ_[p]) from rfl]
  rw [Polynomial.eval₂_at_apply]
  rfl

/-- `aeval`, at the image of an integer, of an integral polynomial. -/
lemma hensel_sf_aeval_int (P : Polynomial ℤ) (y : ℤ) :
    P.aeval ((y : ℤ_[p])) = ((P.eval y : ℤ) : ℤ_[p]) := by
  rw [← hensel_sf_eval_map_int P y, Polynomial.eval_map, Polynomial.aeval_def]

/-- If `p ^ k` divides the integer `d`, then the norm of `d` in `ℤ_[p]` is at most `p^{-k}`. -/
lemma hensel_sf_norm_int_le (d : ℤ) (k : ℕ) (h : ((p ^ k : ℕ) : ℤ) ∣ d) :
    ‖((d : ℤ_[p]))‖ ≤ (p : ℝ) ^ (-(k : ℤ)) :=
  (PadicInt.norm_int_le_pow_iff_dvd).2 (by simpa [Nat.cast_pow] using h)

/-- The norm of an integer whose `p`-adic valuation is exactly `ν`. -/
lemma hensel_sf_norm_int_eq (d : ℤ) (ν : ℕ)
    (h1 : ((p ^ ν : ℕ) : ℤ) ∣ d) (h2 : ¬ ((p ^ (ν + 1) : ℕ) : ℤ) ∣ d) :
    ‖((d : ℤ_[p]))‖ = (p : ℝ) ^ (-(ν : ℤ)) := by
  have hd0 : d ≠ 0 := fun h => h2 (h ▸ dvd_zero _)
  have hne : ((d : ℤ_[p])) ≠ 0 := fun h => hd0 ((PadicInt.intCast_eq d 0).1 h)
  have hle : ((d : ℤ_[p])).valuation ≤ ν := by
    by_contra h
    push Not at h
    have h3 : ‖((d : ℤ_[p]))‖ ≤ (p : ℝ) ^ (-((ν + 1 : ℕ) : ℤ)) :=
      (PadicInt.norm_le_pow_iff_le_valuation _ hne (ν + 1)).2 h
    exact h2 (by simpa [Nat.cast_pow] using (PadicInt.norm_int_le_pow_iff_dvd).1 h3)
  have hge : ν ≤ ((d : ℤ_[p])).valuation :=
    (PadicInt.norm_le_pow_iff_le_valuation _ hne ν).1
      ((PadicInt.norm_int_le_pow_iff_dvd).2 (by simpa [Nat.cast_pow] using h1))
  rw [PadicInt.norm_eq_zpow_neg_valuation hne, le_antisymm hle hge]

end Aux

theorem card_hensel_le_sf {p : ℕ} [Fact p.Prime] (P : Polynomial ℤ) (hP : P ≠ 0) (M : ℕ)
    (hM : 1 ≤ M) : (henselSet p P M).card ≤ P.natDegree := by
  classical
  let u : ℕ → ℤ_[p] := fun y => ((y : ℤ) : ℤ_[p])
  let root : ℕ → ℤ_[p] := fun y =>
    if h : ‖P.aeval (u y)‖ < ‖P.derivative.aeval (u y)‖ ^ 2
    then Classical.choose (hensels_lemma h) else u y
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  -- Each `y ∈ henselSet` admits a root of `P` within `p^{-M}` of `y`.
  have key : ∀ y ∈ henselSet p P M, P.aeval (root y) = 0 ∧
      ‖u y - root y‖ ≤ (p : ℝ) ^ (-(M : ℤ)) := by
    intro y hy
    obtain ⟨-, ν, h1, h2, h3⟩ := Finset.mem_filter.1 hy
    -- the exact norm of the derivative at `y`
    have hD : ‖P.derivative.aeval (u y)‖ = (p : ℝ) ^ (-(ν : ℤ)) := by
      dsimp only [u]
      rw [hensel_sf_aeval_int P.derivative (y : ℤ)]
      exact hensel_sf_norm_int_eq _ ν h1 h2
    -- bound for the value of `P` at `y`
    have hW : ‖P.aeval (u y)‖ ≤ (p : ℝ) ^ (-((max (2 * ν + 1) (M + ν) : ℕ) : ℤ)) := by
      dsimp only [u]
      rw [hensel_sf_aeval_int P (y : ℤ)]
      exact hensel_sf_norm_int_le _ _ h3
    have hMν : ((M + ν : ℕ) : ℤ) ≤ ((max (2 * ν + 1) (M + ν) : ℕ) : ℤ) :=
      Nat.cast_le.mpr (le_max_right (2 * ν + 1) (M + ν))
    have hν₂ : ((2 * ν + 1 : ℕ) : ℤ) ≤ ((max (2 * ν + 1) (M + ν) : ℕ) : ℤ) :=
      Nat.cast_le.mpr (le_max_left (2 * ν + 1) (M + ν))
    have hW1 : ‖P.aeval (u y)‖ ≤ (p : ℝ) ^ (-((M + ν : ℕ) : ℤ)) :=
      hW.trans ((zpow_le_zpow_iff_right₀ hp1).2 (neg_le_neg hMν))
    have hW2 : ‖P.aeval (u y)‖ ≤ (p : ℝ) ^ (-((2 * ν + 1 : ℕ) : ℤ)) :=
      hW.trans ((zpow_le_zpow_iff_right₀ hp1).2 (neg_le_neg hν₂))
    -- Hensel's hypothesis
    have hnorm : ‖P.aeval (u y)‖ < ‖P.derivative.aeval (u y)‖ ^ 2 := by
      rw [hD]
      have hsq : ((p : ℝ) ^ (-(ν : ℤ))) ^ 2 = (p : ℝ) ^ (-((2 * ν : ℕ) : ℤ)) := by
        rw [sq, ← zpow_add₀ (by positivity : (p : ℝ) ≠ 0)]
        congr 1; push_cast; ring
      rw [hsq]
      exact hW2.trans_lt ((zpow_lt_zpow_iff_right₀ hp1).2 (by push_cast; omega))
    have hspec := Classical.choose_spec (hensels_lemma hnorm)
    have hroot_eq : root y = Classical.choose (hensels_lemma hnorm) := by
      dsimp only [root]
      rw [dif_pos hnorm]
    have hroot0 : P.aeval (root y) = 0 := by rw [hroot_eq]; exact hspec.1
    have hDroot : ‖P.derivative.aeval (root y)‖ = (p : ℝ) ^ (-(ν : ℤ)) := by
      rw [hroot_eq, hspec.2.2.1, hD]
    refine ⟨hroot0, ?_⟩
    -- `root y` is close to `y`, and `‖root y - y‖ * ‖P'(root y)‖ = ‖P(y)‖`
    have hlt : ‖u y - root y‖ < ‖P.derivative.aeval (root y)‖ := by
      have h1' : ‖root y - u y‖ < ‖P.derivative.aeval (u y)‖ := by
        rw [hroot_eq]; exact hspec.2.1
      rw [norm_sub_rev, hDroot, ← hD]
      exact h1'
    have hprod : ‖u y - root y‖ * (p : ℝ) ^ (-(ν : ℤ)) = ‖P.aeval (u y)‖ := by
      rw [← hDroot]
      exact aeval_dist_eq_norm P hroot0 hlt
    have hsplit : (p : ℝ) ^ (-((M + ν : ℕ) : ℤ))
        = (p : ℝ) ^ (-(M : ℤ)) * (p : ℝ) ^ (-(ν : ℤ)) := by
      rw [← zpow_add₀ (by positivity : (p : ℝ) ≠ 0)]
      congr 1; push_cast; ring
    have hcancel : ‖u y - root y‖ * (p : ℝ) ^ (-(ν : ℤ))
        ≤ (p : ℝ) ^ (-(M : ℤ)) * (p : ℝ) ^ (-(ν : ℤ)) := by
      rw [hprod, ← hsplit]
      exact hW1
    exact (mul_le_mul_iff_of_pos_right (zpow_pos (by positivity : (0 : ℝ) < p) _)).1 hcancel
  -- distinct elements of `henselSet` have distinct Hensel roots
  have hinj : Set.InjOn root ↑(henselSet p P M) := by
    intro y₁ hy₁ y₂ hy₂ heq
    by_contra hne
    have d₁ := (key y₁ hy₁).2
    have d₂ := (key y₂ hy₂).2
    have hcomb : ‖u y₁ - u y₂‖ ≤ (p : ℝ) ^ (-(M : ℤ)) := by
      have hz : u y₁ - u y₂ = (u y₁ - root y₁) + (root y₁ - u y₂) := by ring
      rw [hz]
      refine (PadicInt.nonarchimedean _ _).trans (max_le d₁ ?_)
      rw [heq, norm_sub_rev]
      exact d₂
    have hcast : ((((y₁ : ℤ) - (y₂ : ℤ)) : ℤ) : ℤ_[p]) = u y₁ - u y₂ := by
      dsimp only [u]; push_cast; ring
    have hdvd : (p ^ M : ℤ) ∣ ((y₁ : ℤ) - (y₂ : ℤ)) :=
      (PadicInt.norm_int_le_pow_iff_dvd).1 (by rw [hcast]; exact hcomb)
    exact hne (eq_of_dvd_sub_of_lt (Finset.mem_range.1 (Finset.mem_filter.1 hy₁).1)
      (Finset.mem_range.1 (Finset.mem_filter.1 hy₂).1) hdvd)
  have hInj : Function.Injective (algebraMap ℤ ℤ_[p]) :=
    fun a b h => (PadicInt.intCast_eq a b).1 h
  have hFne : P.map (algebraMap ℤ ℤ_[p]) ≠ 0 := fun h =>
    hP ((Polynomial.map_eq_zero_iff (f := algebraMap ℤ ℤ_[p]) hInj).1 h)
  have hsub : (henselSet p P M).image root ⊆ (P.map (algebraMap ℤ ℤ_[p])).roots.toFinset := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 ha
    rw [Multiset.mem_toFinset, Polynomial.mem_roots']
    exact ⟨hFne, by
      rw [Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def]
      exact (key y hy).1⟩
  calc (henselSet p P M).card
      = ((henselSet p P M).image root).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ ((P.map (algebraMap ℤ ℤ_[p])).roots.toFinset).card := Finset.card_le_card hsub
    _ ≤ (P.map (algebraMap ℤ ℤ_[p])).roots.card := Multiset.toFinset_card_le _
    _ ≤ (P.map (algebraMap ℤ ℤ_[p])).natDegree := Polynomial.card_roots' _
    _ ≤ P.natDegree := Polynomial.natDegree_map_le

end Work.LinnikBurgess
