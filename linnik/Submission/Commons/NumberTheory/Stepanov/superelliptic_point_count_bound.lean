import Mathlib
import Submission.Commons.NumberTheory.Stepanov.ncard_points_superelliptic
import Submission.Commons.NumberTheory.Stepanov.superelliptic_char_sum_bound

/-!
# Stepanov's bound for the superelliptic point count

Target:

```
∀ e d, 2 ≤ e → 1 ≤ d → ∃ C > 0, ∀ F [Field F] [Fintype F] [DecidableEq F],
  e ∣ #F - 1 → ∀ g : F[X], g.natDegree ≤ d →
    (∀ p prime, p ∣ e → ∀ a h, g ≠ C a * h ^ p) →
    #{(x,y) ∈ F × F | y^e = g x} ≤ #F + C * √#F
```

The proof splits into two parts:

* the exact count `#S = e * T + R₀`, where `T = #{x : g x ^ ((#F-1)/e) = 1}` and
  `R₀ = #{x : g x = 0}` (commons `ncard_points_superelliptic`);
* the Stepanov bound `T ≤ #F / e + C √#F` (Stepanov's elementary method: the auxiliary
  polynomial is built from Hasse derivatives, and the non-degeneracy from the Kummer
  ring `F[X,Y]/(Y^e - g)`); this is the commons lemma `superelliptic_char_sum_bound`.
-/

namespace Commons.NumberTheory.Stepanov

open Polynomial

/-- The point-count bound, deduced from the Stepanov character-sum bound. -/
theorem superelliptic_point_count_bound_of_char_sum_bound.{u}
    (hS : ∀ (e d : ℕ), 2 ≤ e → 1 ≤ d → ∃ C : ℝ, 0 < C ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F], e ∣ Fintype.card F - 1 →
        ∀ g : Polynomial F, g.natDegree ≤ d →
        (∀ p : ℕ, p.Prime → p ∣ e → ∀ (a : F) (h : Polynomial F),
          g ≠ Polynomial.C a * h ^ p) →
        (({x : F | g.eval x ^ ((Fintype.card F - 1) / e) = 1} : Set F).ncard : ℝ)
          ≤ (Fintype.card F : ℝ) / (e : ℝ) + C * Real.sqrt (Fintype.card F))
    (e d : ℕ) (he : 2 ≤ e) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
        e ∣ Fintype.card F - 1 →
        ∀ g : Polynomial F, g.natDegree ≤ d →
        (∀ p : ℕ, p.Prime → p ∣ e → ∀ (a : F) (h : Polynomial F),
          g ≠ Polynomial.C a * h ^ p) →
        (({p : F × F | p.2 ^ e = g.eval p.1} : Set (F × F)).ncard : ℝ)
          ≤ (Fintype.card F : ℝ) + C * Real.sqrt (Fintype.card F) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := hS e d he hd
  refine ⟨(e : ℝ) * C₀ + (d : ℝ), by positivity, ?_⟩
  intro F _ _ _ hdiv g hgd hnd
  -- `g ≠ 0` (take the prime factor of `e` and `h = 0`)
  have hg0 : g ≠ 0 := by
    obtain ⟨p, hp, hpe⟩ := Nat.exists_prime_and_dvd (by omega : e ≠ 1)
    intro h0
    exact hnd p hp hpe 0 0 (by rw [h0]; simp)
  -- the exact point count
  have hpc := ncard_points_superelliptic F e (by omega) hdiv g
  -- the roots of `g` contribute at most `deg g ≤ d`
  have hroot : (({a : F | g.eval a = 0} : Set F).ncard : ℝ) ≤ (d : ℝ) := by
    have hsub : ({a : F | g.eval a = 0} : Set F) ⊆ (↑(g.roots.toFinset) : Set F) := by
      intro a ha
      rw [Set.mem_ofPred_eq] at ha
      simp only [Multiset.mem_toFinset, Finset.mem_coe]
      rw [Polynomial.mem_roots hg0]
      exact ha
    have h1 : ({a : F | g.eval a = 0} : Set F).ncard ≤ (↑(g.roots.toFinset) : Set F).ncard :=
      Set.ncard_le_ncard hsub
    have h2 : (↑(g.roots.toFinset) : Set F).ncard = g.roots.toFinset.card :=
      Set.ncard_coe_finset _
    have h3 : g.roots.toFinset.card ≤ g.natDegree :=
      (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' g)
    have h4 : ({a : F | g.eval a = 0} : Set F).ncard ≤ g.natDegree := by
      rw [h2] at h1; exact h1.trans h3
    exact (Nat.cast_le.mpr h4).trans (by exact_mod_cast hgd)
  have hT := hC₀ F hdiv g hgd hnd
  have hq1 : (1 : ℝ) ≤ Real.sqrt (Fintype.card F) := by
    rw [Real.one_le_sqrt]
    have h2 : (1 : ℕ) ≤ Fintype.card F := le_of_lt (Fintype.one_lt_card)
    exact_mod_cast h2
  have hT' : (e : ℝ) * (({x : F | g.eval x ^ ((Fintype.card F - 1) / e) = 1} : Set F).ncard : ℝ)
      ≤ (Fintype.card F : ℝ) + (e : ℝ) * C₀ * Real.sqrt (Fintype.card F) := by
    have h := mul_le_mul_of_nonneg_left hT (show (0:ℝ) ≤ e by positivity)
    rw [mul_add, mul_div_cancel₀ _ (by exact_mod_cast (by omega : e ≠ 0))] at h
    linarith [h]
  have hroot' : (({a : F | g.eval a = 0} : Set F).ncard : ℝ)
      ≤ (d : ℝ) * Real.sqrt (Fintype.card F) := by
    nlinarith [hroot, hq1, Nat.cast_nonneg (α := ℝ) d]
  rw [hpc]
  push_cast
  linarith [hT', hroot']

/-- **Stepanov's bound for the superelliptic point count** `y ^ e = g x`: the number of
`F`-points is at most `#F + C √#F`, with `C` depending only on `e` and `deg g`. -/
theorem superelliptic_point_count_bound :
    ∀ (e d : ℕ), 2 ≤ e → 1 ≤ d → ∃ C : ℝ, 0 < C ∧
      ∀ (F : Type*) [Field F] [Fintype F] [DecidableEq F],
        e ∣ Fintype.card F - 1 →
        ∀ g : Polynomial F, g.natDegree ≤ d →
        (∀ p : ℕ, p.Prime → p ∣ e → ∀ (a : F) (h : Polynomial F),
          g ≠ Polynomial.C a * h ^ p) →
        (({p : F × F | p.2 ^ e = g.eval p.1} : Set (F × F)).ncard : ℝ)
          ≤ (Fintype.card F : ℝ) + C * Real.sqrt (Fintype.card F) := by
  intro e d he hd
  exact superelliptic_point_count_bound_of_char_sum_bound
    (fun e d he hd => superelliptic_char_sum_bound e d he hd) e d he hd

end Commons.NumberTheory.Stepanov
