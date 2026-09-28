import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.kwin_spec
import Submission.Work.HP.Sig2.num_lattices_of
import Submission.Work.HP.Sig2.Tset_finite

/-!
# The dyadic-window fibre bound for `quartic44` (`Work.HP.Q44Main.q44_window_fiber_le`)

Fix a Minkowski constant `Kmink ≥ 1` satisfying `∏_{j<rk L} λ_{j+1}(L) ≤ Kmink · detL L` for
every integral lattice `L ⊆ ℤ⁵`.  For a dyadic window `k : Fin 3 → ℕ`, put
`kwin 3 L j = ⌈log₂ λ_{j+1}(L)⌉`.  The theorem bounds the `k`-window contribution

`Σ_{L ∈ T, kwin 3 L = k} λ₁(L)¹⁸ λ₂(L)¹⁸ λ₃(L)²⁰`

of any finite family `T` of primitive rank-`3` sublattices of `ℤ⁵` by
`Knum · 2^{25 k₀ + 23 k₁ + 23 k₂}`, uniformly in `k` and `T`.

There are two ingredients, exactly as in the paper's dyadic summation:

* **Pointwise bound.**  A lattice of the window satisfies `λ_{j+1}(L) ≤ 2^{k_j}`
  (`kwin_spec`), hence `λ₁¹⁸λ₂¹⁸λ₃²⁰ ≤ 2^{18k₀+18k₁+20k₂}`.
* **Counting.**  The lattices of the window form a subset of
  `{L : IsPrimLat L ∧ rk L = 3 ∧ ∀ j, λ_{j+1}(L) ≤ 2^{k_j}}`, whose cardinality is at most
  `K · ∏_j (2^{k_j})^{5+3+1-2(j+1)} = K · 2^{7k₀+5k₁+3k₂}` by the paper's "number of lattices"
  theorem `num_lattices_of` (the exponents are `N + r + 1 - 2j` with `N = 5`, `r = 3`), the
  finiteness input being `Tset_finite`.

Multiplying, `2^{(7+18)k₀ + (5+18)k₁ + (3+20)k₂} = 2^{25k₀+23k₁+23k₂}`.
-/

set_option autoImplicit false
noncomputable section

namespace Work.HP.Q44Main

open Work.HP

/-- Exponent arithmetic of the window count: with `N = 5`, `r = 3` the `num_lattices_of`
exponents are `5 + 3 + 1 - 2(j+1) = 7, 5, 3` for `j = 0, 1, 2`, so
`∏_{j<3} (2^{k_j})^{5+3+1-2(j+1)} = 2^{7k₀+5k₁+3k₂}`. -/
lemma q44_window_prod (k : Fin 3 → ℕ) :
    (∏ j : Fin 3, ((2 : ℝ) ^ (k j)) ^ (5 + 3 + 1 - 2 * (j.1 + 1)))
      = (2 : ℝ) ^ (7 * k 0 + 5 * k 1 + 3 * k 2) := by
  rw [Fin.prod_univ_three]
  simp only [Fin.val_zero, Fin.val_one', Fin.val_two]
  rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
  ring

/-- Exponent arithmetic of the pointwise bound: `λ_{j+1} ≤ 2^{k_j}` gives
`λ₁¹⁸λ₂¹⁸λ₃²⁰ ≤ 2^{18k₀+18k₁+20k₂}`; combined with the count `2^{7k₀+5k₁+3k₂}` this is
`2^{25k₀+23k₁+23k₂}`. -/
lemma q44_window_exp (k : Fin 3 → ℕ) :
    (2 : ℝ) ^ (7 * k 0 + 5 * k 1 + 3 * k 2) * (2 : ℝ) ^ (18 * k 0 + 18 * k 1 + 20 * k 2)
      = (2 : ℝ) ^ (25 * k 0 + 23 * k 1 + 23 * k 2) := by
  rw [← pow_add]
  congr 1
  ring

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
  -- The paper's count of lattices in a window.
  obtain ⟨K, hKpos, hK⟩ := Work.HP.Sig2.num_lattices_of (ι := Fin 5) Kmink hKmink0 hmink
  refine ⟨K, hKpos, ?_⟩
  intro k T hT
  classical
  set S : Finset (Submodule ℤ (Fin 5 → ℤ)) := T.filter (fun L => Work.HP.kwin 3 L = k) with hSdef
  -- Pointwise bound on a single summand.
  have hpoint : ∀ L ∈ S,
      Work.HP.lam L 1 ^ 18 * Work.HP.lam L 2 ^ 18 * Work.HP.lam L 3 ^ 20
        ≤ (2 : ℝ) ^ (18 * k 0 + 18 * k 1 + 20 * k 2) := by
    intro L hL
    rw [hSdef, Finset.mem_filter] at hL
    obtain ⟨hLT, hLk⟩ := hL
    obtain ⟨-, hrk⟩ := hT L hLT
    have hspec := (Work.HP.kwin_spec (Fin 5) 3 L (by norm_num) hrk).1
    have h1 : Work.HP.lam L 1 ≤ (2 : ℝ) ^ (k 0) := by
      have h := hspec ⟨0, by norm_num⟩
      rw [hLk] at h
      simpa using h
    have h2 : Work.HP.lam L 2 ≤ (2 : ℝ) ^ (k 1) := by
      have h := hspec ⟨1, by norm_num⟩
      rw [hLk] at h
      simpa using h
    have h3 : Work.HP.lam L 3 ≤ (2 : ℝ) ^ (k 2) := by
      have h := hspec ⟨2, by norm_num⟩
      rw [hLk] at h
      simpa using h
    have e1 : Work.HP.lam L 1 ^ 18 ≤ (2 : ℝ) ^ (18 * k 0) := by
      calc Work.HP.lam L 1 ^ 18 ≤ ((2 : ℝ) ^ (k 0)) ^ 18 :=
            pow_le_pow_left₀ (Work.HP.lam_nonneg L 1) h1 18
        _ = (2 : ℝ) ^ (18 * k 0) := by rw [← pow_mul]; ring
    have e2 : Work.HP.lam L 2 ^ 18 ≤ (2 : ℝ) ^ (18 * k 1) := by
      calc Work.HP.lam L 2 ^ 18 ≤ ((2 : ℝ) ^ (k 1)) ^ 18 :=
            pow_le_pow_left₀ (Work.HP.lam_nonneg L 2) h2 18
        _ = (2 : ℝ) ^ (18 * k 1) := by rw [← pow_mul]; ring
    have e3 : Work.HP.lam L 3 ^ 20 ≤ (2 : ℝ) ^ (20 * k 2) := by
      calc Work.HP.lam L 3 ^ 20 ≤ ((2 : ℝ) ^ (k 2)) ^ 20 :=
            pow_le_pow_left₀ (Work.HP.lam_nonneg L 3) h3 20
        _ = (2 : ℝ) ^ (20 * k 2) := by rw [← pow_mul]; ring
    calc Work.HP.lam L 1 ^ 18 * Work.HP.lam L 2 ^ 18 * Work.HP.lam L 3 ^ 20
        ≤ (2 : ℝ) ^ (18 * k 0) * (2 : ℝ) ^ (18 * k 1) * (2 : ℝ) ^ (20 * k 2) := by
          exact mul_le_mul (mul_le_mul e1 e2 (by positivity) (by positivity)) e3
            (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (18 * k 0 + 18 * k 1 + 20 * k 2) := by rw [← pow_add, ← pow_add]
  -- Counting bound on the window.
  have hcount : (S.card : ℝ) ≤ K * (2 : ℝ) ^ (7 * k 0 + 5 * k 1 + 3 * k 2) := by
    have hsub : (↑S : Set (Submodule ℤ (Fin 5 → ℤ))) ⊆
        {L | Work.HP.IsPrimLat L ∧ Work.HP.rk L = 3 ∧
          ∀ j : Fin 3, Work.HP.lam L (j.1 + 1) ≤ (2 : ℝ) ^ (k j)} := by
      intro L hL
      rw [Finset.mem_coe, hSdef, Finset.mem_filter] at hL
      obtain ⟨hLT, hLk⟩ := hL
      obtain ⟨hprim, hrk⟩ := hT L hLT
      refine ⟨hprim, hrk, fun j => ?_⟩
      have h := (Work.HP.kwin_spec (Fin 5) 3 L (by norm_num) hrk).1 j
      rw [hLk] at h
      exact h
    have hfin : ({L | Work.HP.IsPrimLat L ∧ Work.HP.rk L = 3 ∧
          ∀ j : Fin 3, Work.HP.lam L (j.1 + 1) ≤ (2 : ℝ) ^ (k j)} :
            Set (Submodule ℤ (Fin 5 → ℤ))).Finite :=
      Work.HP.Sig2.Tset_finite (ι := Fin 5) 3 (fun j : Fin 3 => (2 : ℝ) ^ (k j))
    have h1 : ((↑S : Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ) ≤
        ((({L | Work.HP.IsPrimLat L ∧ Work.HP.rk L = 3 ∧
          ∀ j : Fin 3, Work.HP.lam L (j.1 + 1) ≤ (2 : ℝ) ^ (k j)} :
            Set (Submodule ℤ (Fin 5 → ℤ)))).ncard : ℝ) :=
      by exact_mod_cast Set.ncard_le_ncard hsub hfin
    have h2 : ((({L | Work.HP.IsPrimLat L ∧ Work.HP.rk L = 3 ∧
          ∀ j : Fin 3, Work.HP.lam L (j.1 + 1) ≤ (2 : ℝ) ^ (k j)} :
            Set (Submodule ℤ (Fin 5 → ℤ)))).ncard : ℝ) ≤
        K * (∏ j : Fin 3, ((2 : ℝ) ^ (k j)) ^ (5 + 3 + 1 - 2 * (j.1 + 1))) := by
      simpa only [Fintype.card_fin] using
        hK 3 (fun j : Fin 3 => (2 : ℝ) ^ (k j))
          (fun j => one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    have h3 : (S.card : ℝ) =
        ((↑S : Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ) := by
      rw [Set.ncard_coe_finset]
    rw [h3]
    refine (h1.trans h2).trans (le_of_eq ?_)
    rw [q44_window_prod]
  calc (∑ L ∈ S,
        Work.HP.lam L 1 ^ 18 * Work.HP.lam L 2 ^ 18 * Work.HP.lam L 3 ^ 20)
      ≤ ∑ L ∈ S, (2 : ℝ) ^ (18 * k 0 + 18 * k 1 + 20 * k 2) :=
        Finset.sum_le_sum hpoint
    _ = (S.card : ℝ) * (2 : ℝ) ^ (18 * k 0 + 18 * k 1 + 20 * k 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ K * (2 : ℝ) ^ (7 * k 0 + 5 * k 1 + 3 * k 2)
          * (2 : ℝ) ^ (18 * k 0 + 18 * k 1 + 20 * k 2) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = K * (2 : ℝ) ^ (25 * k 0 + 23 * k 1 + 23 * k 2) := by
        rw [mul_assoc, q44_window_exp]

end Work.HP.Q44Main
