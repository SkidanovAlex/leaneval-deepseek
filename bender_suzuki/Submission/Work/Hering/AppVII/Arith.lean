import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Arithmetic ingredient of Appendix VII (Part 2), step 6

Peterfalvi, Appendix VII, p. 220, step 6: with `q` an odd prime, `m ≥ 1`, and `n₁, …, n_p`
nonnegative integers (p prime) whose values are all equal except at one index where the value
differs by `±1`, and with `Σ nᵢ = q^m`, every `nᵢ` is nonzero.  (This is what rules out the
"extra" irreducible constituent of `Res_P χ` in the last line of the proof.)
-/

namespace Work.Hering.AppVII

/-! ## The elementary integer lemma of step 5 (p. 219), still to be proved

    theorem arith_sum_sq {p : ℕ} (hp : 2 ≤ p) {n : Fin p → ℤ} (hne : ∃ i j, n i ≠ n j) :
      (∑ i : Fin p, ∑ j : Fin p, (n i - n j) ^ 2 = 2 * ((p : ℤ) - 1)) ↔
        ∃ i₀ : Fin p, ∃ m : ℤ, (∀ i : Fin p, i ≠ i₀ → n i = m) ∧
          (n i₀ = m + 1 ∨ n i₀ = m - 1)

(`Σ_{i,j} (nᵢ-nⱼ)² = 2 Σ_{i<j} (nᵢ-nⱼ)²`, so the equation is `Σ_{i<j}(nᵢ-nⱼ)² = p - 1`.)

* `⇐` is a direct computation: with all entries equal to `m` except one equal to `m ± 1`, only
  the `2(p-1)` ordered pairs involving the exceptional index contribute, each `1`.
* `⇒`: translate so that the minimum is `0` (the sum is translation invariant).  With `z` zero
  entries and `q = p - z` positive entries, the double sum is at least `2 · z · Σ_{nⱼ>0} nⱼ²`
  (only the ordered pairs (zero, positive) are used) and `Σ_{nⱼ>0} nⱼ² ≥ q`, so
  `z·q ≤ p - 1 = z + q - 1`, i.e. `(z-1)(q-1) ≤ 0`, hence `z = 1` or `q = 1`.
  If `q = 1` the single positive value `u` has `(p-1)u² = p - 1`, so `u = 1`; if `z = 1` then
  `Σ_{nⱼ>0} nⱼ² ≤ p - 1 = q` while `q` summands are each `≥ 1`, so every nonzero entry is `1`.
  Translating back gives the stated structure. -/

/-- **Appendix VII, step 6 (p. 220).** -/
theorem arith_step6 {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (hqodd : Odd q) (hm : 1 ≤ m)
    {n : Fin p → ℤ} (hnn : ∀ i : Fin p, 0 ≤ n i) (hsum : ∑ i : Fin p, n i = (q : ℤ) ^ m)
    (hstruct : ∃ i₀ : Fin p, ∃ m' : ℤ, (∀ i : Fin p, i ≠ i₀ → n i = m') ∧
      (n i₀ = m' + 1 ∨ n i₀ = m' - 1)) : ∀ i : Fin p, n i ≠ 0 := by
  classical
  obtain ⟨i₀, c, hrest, hsp⟩ := hstruct
  have hp2 : 2 ≤ p := hp.two_le
  -- there is an index different from `i₀`
  obtain ⟨j, hj⟩ : ∃ j : Fin p, j ≠ i₀ := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset (Fin p)) ⊆ {i₀} := by
      intro x _; simp [hcon x]
    have hle : (Finset.univ : Finset (Fin p)).card ≤ 1 :=
      (Finset.card_le_card hsub).trans (by simp)
    simp at hle
    omega
  have hc0 : 0 ≤ c := by
    have h := hnn j
    rwa [hrest j hj] at h
  -- the total sum, in terms of `c`
  have hsumsplit : ∑ i : Fin p, n i = ((p : ℤ) - 1) * c + n i₀ := by
    rw [← Finset.sum_erase_add (Finset.univ) n (Finset.mem_univ i₀)]
    have hcongr : (Finset.univ.erase i₀).sum n = (Finset.univ.erase i₀).sum (fun _ => c) :=
      Finset.sum_congr rfl (fun i hi => hrest i (Finset.mem_erase.mp hi).1)
    have h1 : (Finset.univ.erase i₀).sum (fun _ => c) = ((p : ℤ) - 1) * c := by
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i₀),
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hp1 : 1 ≤ p := hp.one_le
      rw [Nat.cast_sub hp1]
      ring
    rw [hcongr, h1]
  -- `q ^ m ≥ 3`
  have hq3 : 3 ≤ q := by
    have h2 : 2 ≤ q := hq.two_le
    have hne : q ≠ 2 := by
      intro hcon
      rw [hcon] at hqodd
      exact absurd hqodd (by decide)
    omega
  have hqm : (3 : ℤ) ≤ (q : ℤ) ^ m := by
    have h3 : (3 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq3
    have h4 : (q : ℤ) ^ (1 : ℕ) ≤ (q : ℤ) ^ m :=
      pow_le_pow_right₀ (by linarith : (1 : ℤ) ≤ (q : ℤ)) hm
    rw [pow_one] at h4
    linarith
  intro i hi
  by_cases hii : i = i₀
  · -- the exceptional index
    subst hii
    rcases hsp with h1 | h1
    · have hc : c = -1 := by omega
      have hval : (q : ℤ) ^ m = -(((p : ℤ)) - 1) := by
        rw [← hsum, hsumsplit, h1, hc]; ring
      have hp1 : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.one_le
      linarith
    · have hc : c = 1 := by omega
      have hzeq : ((p : ℤ) - 1) = (q : ℤ) ^ m := by
        have h2 : (q : ℤ) ^ m = ((p : ℤ) - 1) * 1 + 0 := by
          rw [← hsum, hsumsplit, h1, hc]; ring
        linarith
      -- parity: `q ^ m` is odd, so `p` is even, so `p = 2`, so `q ^ m = 1 < 3`
      have hcast : ((q : ℤ)) ^ m = ((q ^ m : ℕ) : ℤ) := by push_cast; ring
      have hpnat : p = q ^ m + 1 := by
        have h3 : (p : ℤ) = ((q ^ m : ℕ) : ℤ) + 1 := by
          rw [← hcast]; linarith
        omega
      have hEven : Even p := by
        rw [hpnat]
        exact hqodd.pow.add_one
      rcases hp.eq_two_or_odd' with htwo | hodd
      · rw [htwo] at hpnat
        have h1' : q ^ m = 1 := by omega
        have hlt : 1 < q ^ m := one_lt_pow' (by omega) (by omega)
        omega
      · obtain ⟨k, hk⟩ := hodd
        obtain ⟨l, hl⟩ := hEven
        omega
  · -- all other indices
    rw [hrest i hii] at hi
    rcases hsp with h1 | h1
    · have hval : (q : ℤ) ^ m = n i₀ := by
        rw [← hsum, hsumsplit, hi]; ring
      rw [h1] at hval
      linarith
    · have hval : (q : ℤ) ^ m = n i₀ := by
        rw [← hsum, hsumsplit, hi]; ring
      rw [h1] at hval
      linarith

end Work.Hering.AppVII
