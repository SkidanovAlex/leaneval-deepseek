import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.kwin_spec
import Submission.Work.HP.Sig2.num_lattices_of
import Submission.Work.HP.Sig2.Tset_finite

/-!
# The dyadic-window fibre bound for the quartic threefold case (`q44_window_fiber_le`)

Fix the Minkowski constant `Kmink`.  `q44_window_fiber_le` bounds, uniformly in the window
`k : Fin 3 → ℕ` and in the finite family `T` of primitive rank-`3` sublattices of `ℤ⁵`, the
contribution of the `k`-window

`Σ_{L ∈ T, kwin 3 L = k} λ₁(L)¹⁸ λ₂(L)¹⁸ λ₃(L)²⁰`

by `Knum · 2^{25 k₀ + 23 k₁ + 23 k₂}`.

The two ingredients are

* **counting** (`num_lattices_of`): inside a dyadic window, `#T ≤ K · 2^{7 k₀ + 5 k₁ + 3 k₂}`,
  because a primitive rank-`3` lattice with `kwin 3 L = k` satisfies `λ_{j+1} ≤ 2^{k_j}` and
  `num_lattices_of` (with `N = card (Fin 5) = 5`, `r = 3`) bounds the number of such lattices by
  `K · ∏_j (2^{k_j})^{5+3+1-2(j+1)} = K · 2^{7k₀+5k₁+3k₂}` (the product identity
  `q44_window_prod`);
* **the pointwise bound** `λ₁¹⁸ λ₂¹⁸ λ₃²⁰ ≤ 2^{18k₀+18k₁+20k₂}`, which is again
  `λ_{j+1} ≤ 2^{k_j}` from `kwin_spec` (`kwin_spec`'s first component).

Multiplying gives `2^{(7+18)k₀ + (5+18)k₁ + (3+20)k₂} = 2^{25k₀+23k₁+23k₂}`, as claimed.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.MDEstimates

open Work.HP

/-- The exponent arithmetic of the fibre count: for every dyadic window `k`,
`∏_{j<3} (2^{k_j})^{5+3+1-2(j+1)} = 2^{7k₀+5k₁+3k₂}`.  The three factors are the
`num_lattices_of` exponents `7, 5, 3` attached to `k₀, k₁, k₂`. -/
lemma q44_window_prod (k : Fin 3 → ℕ) :
    (∏ j : Fin 3, ((2 : ℝ) ^ (k j)) ^ (5 + 3 + 1 - 2 * (j.1 + 1)))
      = (2 : ℝ) ^ (7 * k 0 + 5 * k 1 + 3 * k 2) := by
  rw [Fin.prod_univ_three]
  simp only [Fin.val_zero, Fin.val_one', Fin.val_two]
  rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
  ring

/-- **Dyadic-window fibre bound for the quartic threefold case.**  There is a constant `Knum`
(depending only on the Minkowski constant `Kmink`, hence on nothing else) such that for every
dyadic window `k : Fin 3 → ℕ` and every finite family `T` of primitive rank-`3` sublattices of
`ℤ⁵`, the sum of `λ₁¹⁸ λ₂¹⁸ λ₃²⁰` over the `k`-window is at most
`Knum · 2^{25 k₀ + 23 k₁ + 23 k₂}`. -/
theorem q44_window_fiber_le (Kmink : ℝ) (hKmink : 1 ≤ Kmink)
    (hmink : ∀ L : Submodule ℤ (Fin 5 → ℤ),
      (∏ j ∈ Finset.range (Work.HP.rk L), Work.HP.lam L (j + 1)) ≤ Kmink * Work.HP.detL L) :
    ∃ Knum : ℝ, 0 < Knum ∧
      ∀ (k : Fin 3 → ℕ) (T : Finset (Submodule ℤ (Fin 5 → ℤ))),
        (∀ L ∈ T, Work.HP.IsPrimLat L ∧ Work.HP.rk L = 3) →
        (∑ L ∈ T.filter (fun L => Work.HP.kwin 3 L = k),
            Work.HP.lam L 1 ^ 18 * Work.HP.lam L 2 ^ 18 * Work.HP.lam L 3 ^ 20)
          ≤ Knum * (2 : ℝ) ^ (25 * k 0 + 23 * k 1 + 23 * k 2) := by
  have hKmink0 : 0 ≤ Kmink := le_trans zero_le_one hKmink
  obtain ⟨K, hKpos, hK⟩ := Work.HP.Sig2.num_lattices_of (ι := Fin 5) Kmink hKmink0 hmink
  refine ⟨K, hKpos, ?_⟩
  intro k T hT
  set S := T.filter (fun L => Work.HP.kwin 3 L = k) with hSdef
  -- Pointwise bound on a single summand.
  have hbnd : ∀ L ∈ S, Work.HP.lam L 1 ^ 18 * Work.HP.lam L 2 ^ 18 * Work.HP.lam L 3 ^ 20
      ≤ (2:ℝ)^(18 * k 0 + 18 * k 1 + 20 * k 2) := by
    intro L hL
    rw [hSdef, Finset.mem_filter] at hL
    obtain ⟨hLT, hkL⟩ := hL
    obtain ⟨hprim, hrk⟩ := hT L hLT
    have hspec := (Work.HP.kwin_spec (Fin 5) 3 L (by norm_num) hrk).1
    have h1 : Work.HP.lam L 1 ≤ (2:ℝ)^(k 0) := by
      have h := hspec ⟨0, by norm_num⟩
      rw [hkL] at h; simpa using h
    have h2 : Work.HP.lam L 2 ≤ (2:ℝ)^(k 1) := by
      have h := hspec ⟨1, by norm_num⟩
      rw [hkL] at h; simpa using h
    have h3 : Work.HP.lam L 3 ≤ (2:ℝ)^(k 2) := by
      have h := hspec ⟨2, by norm_num⟩
      rw [hkL] at h; simpa using h
    have e1 : Work.HP.lam L 1 ^ 18 ≤ (2:ℝ)^(18 * k 0) := by
      calc Work.HP.lam L 1 ^ 18 ≤ ((2:ℝ)^(k 0))^18 :=
            pow_le_pow_left₀ (Work.HP.lam_nonneg L 1) h1 18
        _ = (2:ℝ)^(18 * k 0) := by rw [← pow_mul]; ring
    have e2 : Work.HP.lam L 2 ^ 18 ≤ (2:ℝ)^(18 * k 1) := by
      calc Work.HP.lam L 2 ^ 18 ≤ ((2:ℝ)^(k 1))^18 :=
            pow_le_pow_left₀ (Work.HP.lam_nonneg L 2) h2 18
        _ = (2:ℝ)^(18 * k 1) := by rw [← pow_mul]; ring
    have e3 : Work.HP.lam L 3 ^ 20 ≤ (2:ℝ)^(20 * k 2) := by
      calc Work.HP.lam L 3 ^ 20 ≤ ((2:ℝ)^(k 2))^20 :=
            pow_le_pow_left₀ (Work.HP.lam_nonneg L 3) h3 20
        _ = (2:ℝ)^(20 * k 2) := by rw [← pow_mul]; ring
    calc Work.HP.lam L 1 ^ 18 * Work.HP.lam L 2 ^ 18 * Work.HP.lam L 3 ^ 20
        ≤ (2:ℝ)^(18 * k 0) * (2:ℝ)^(18 * k 1) * (2:ℝ)^(20 * k 2) := by
          apply mul_le_mul
          · exact mul_le_mul e1 e2 (pow_nonneg (Work.HP.lam_nonneg L 2) 18) (by positivity)
          · exact e3
          · positivity
          · positivity
      _ = (2:ℝ)^(18 * k 0 + 18 * k 1 + 20 * k 2) := by rw [← pow_add, ← pow_add]
  -- Counting bound on the window.
  have hcard : (S.card : ℝ) ≤ K * (2:ℝ)^(7 * k 0 + 5 * k 1 + 3 * k 2) := by
    have hsub : (↑S : Set (Submodule ℤ (Fin 5 → ℤ))) ⊆
        {L | Work.HP.IsPrimLat L ∧ Work.HP.rk L = 3 ∧
          ∀ j : Fin 3, Work.HP.lam L (j.1+1) ≤ (2:ℝ)^(k j)} := by
      intro L hL
      rw [Finset.mem_coe, hSdef, Finset.mem_filter] at hL
      obtain ⟨hLT, hkL⟩ := hL
      obtain ⟨hprim, hrk⟩ := hT L hLT
      refine ⟨hprim, hrk, ?_⟩
      intro j
      have h := (Work.HP.kwin_spec (Fin 5) 3 L (by norm_num) hrk).1 j
      rw [hkL] at h
      exact h
    have h1 : ((↑S : Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ) ≤
        ((({L | Work.HP.IsPrimLat L ∧ Work.HP.rk L = 3 ∧
          ∀ j : Fin 3, Work.HP.lam L (j.1+1) ≤ (2:ℝ)^(k j)} :
            Set (Submodule ℤ (Fin 5 → ℤ)))).ncard : ℝ) := by
      have hfin : ({L | Work.HP.IsPrimLat L ∧ Work.HP.rk L = 3 ∧
          ∀ j : Fin 3, Work.HP.lam L (j.1+1) ≤ (2:ℝ)^(k j)} :
            Set (Submodule ℤ (Fin 5 → ℤ))).Finite :=
        Work.HP.Sig2.Tset_finite (ι := Fin 5) 3 (fun j : Fin 3 => (2:ℝ)^(k j))
      exact_mod_cast Set.ncard_le_ncard hsub hfin
    have hK3 : ((({L | Work.HP.IsPrimLat L ∧ Work.HP.rk L = 3 ∧
          ∀ j : Fin 3, Work.HP.lam L (j.1+1) ≤ (2:ℝ)^(k j)} :
            Set (Submodule ℤ (Fin 5 → ℤ)))).ncard : ℝ) ≤
        K * (∏ j : Fin 3, ((2:ℝ)^(k j))^(5 + 3 + 1 - 2 * (j.1 + 1))) := by
      simpa only [Fintype.card_fin] using
        hK 3 (fun j : Fin 3 => (2:ℝ)^(k j)) (fun j => one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
    have hSc : (S.card : ℝ) = ((↑S : Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ) := by
      rw [Set.ncard_coe_finset]
    rw [hSc]
    refine (h1.trans hK3).trans (le_of_eq ?_)
    rw [q44_window_prod]
  calc ∑ L ∈ S, (Work.HP.lam L 1 ^ 18 * Work.HP.lam L 2 ^ 18 * Work.HP.lam L 3 ^ 20)
      ≤ ∑ L ∈ S, (2:ℝ)^(18 * k 0 + 18 * k 1 + 20 * k 2) := Finset.sum_le_sum hbnd
    _ = (S.card : ℝ) * (2:ℝ)^(18 * k 0 + 18 * k 1 + 20 * k 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ K * (2:ℝ)^(7 * k 0 + 5 * k 1 + 3 * k 2) * (2:ℝ)^(18 * k 0 + 18 * k 1 + 20 * k 2) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = K * (2:ℝ)^(25 * k 0 + 23 * k 1 + 23 * k 2) := by
        rw [mul_assoc, ← pow_add]; ring

end Work.HP.MDEstimates
