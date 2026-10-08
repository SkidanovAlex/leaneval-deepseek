import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.HardCore

/-- Conjugation distributes over powers: `(g * x * g⁻¹) ^ n = g * x ^ n * g⁻¹`. -/
private lemma conj_pow_expand {G : Type*} [Group G] (g x : G) (n : ℕ) :
    (g * x * g⁻¹) ^ n = g * x ^ n * g⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, pow_succ]; group

/-- **Step 5 of Peterfalvi I, Ch. IV §3, Prop. 2** (the abelian case of the hard core of
Hering's theorem): the element `c₁ = (s * t) ^ 4` is inverted by both `s` and `t`.

Write `c₁' = (t * s) ^ 4 = t * c₁ * t⁻¹`.  Two elementary computations give

* `s * c₁ * s⁻¹ = c₁'` (using `s * s = v₀ ∈ C` and `s⁻¹ = s * v₀⁻¹`), and
* `s * c₁' * s⁻¹ = c₁`;

so `d := c₁ * c₁' ∈ C` is fixed by conjugation by `s`.  Conjugation by `t` acts on `C` as an
involution (because `t * t ∈ C` with `C` abelian), so `t * c₁ * t⁻¹ = c₁'` and
`t * c₁' * t⁻¹ = c₁`, whence `d` is also fixed by `t`.  If `d ≠ 1`, the descent hypothesis
`hdesc` produces `k` with `x := d ^ 2 ^ k ∈ V \ {1}`; since `s` and `t` fix `d` they fix `x`, so
`hfix` gives `x = v₀`:

* for `k = 0` this is `d = v₀`, and then `s * c₁ * s⁻¹ * c₁ = d = s * s` contradicts
  `hconstraint` at `c = c₁`;
* for `k = j+1` the element `c := d ^ 2 ^ j ∈ C` satisfies
  `s * c * s⁻¹ * c = c * c = d ^ 2 ^ (j+1) = v₀ = s * s`, again contradicting `hconstraint`.

Hence `d = 1`, i.e. `c₁' = c₁⁻¹`, and both assertions follow. -/
theorem conj_c1_inv {G : Type*} [Group G] {V C : Subgroup G} (hCn : C.Normal)
    (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) {s t c₁ v₀ : G} (hc₁ : c₁ ∈ C)
    (hv₀C : v₀ ∈ C) (hs2 : s * s = v₀) (ht2 : t * t ∈ C) (hc₁def : c₁ = (s * t) ^ 4)
    (hfix : ∀ x : G, x ∈ V → s * x * s⁻¹ = x → t * x * t⁻¹ = x → x = 1 ∨ x = v₀)
    (hconstraint : ¬ ∃ c ∈ C, s * c * s⁻¹ * c = s * s)
    (hdesc : ∀ x ∈ C, x ≠ 1 → ∃ k : ℕ, x ^ (2 ^ k) ∈ V ∧ x ^ (2 ^ k) ≠ 1) :
    s * c₁ * s⁻¹ = c₁⁻¹ ∧ t * c₁ * t⁻¹ = c₁⁻¹ := by
  -- `s⁻¹ = s * v₀⁻¹`, since `s * s = v₀`.
  have hs_inv : s⁻¹ = s * v₀⁻¹ :=
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hs2, mul_inv_cancel])
  -- `(t * s) ^ 4 ∈ C`, being `t * c₁ * t⁻¹`.
  have hts4C : (t * s) ^ 4 ∈ C := by
    have h1 : (t * s) ^ 4 = t * (s * t) ^ 4 * t⁻¹ := by
      rw [← conj_pow_expand t (s * t) 4]
      congr 1
      group
    rw [h1, ← hc₁def]
    exact hCn.conj_mem c₁ hc₁ t
  -- `s * c₁ * s⁻¹ = (t * s) ^ 4`.
  have hs_conj : s * c₁ * s⁻¹ = (t * s) ^ 4 := by
    have h1 : s * (s * t) * s⁻¹ = v₀ * (t * s) * v₀⁻¹ := by
      rw [← mul_assoc s s t, hs2, hs_inv]
      group
    rw [hc₁def, ← conj_pow_expand s (s * t) 4, h1, conj_pow_expand v₀ (t * s) 4]
    rw [hCab v₀ hv₀C ((t * s) ^ 4) hts4C]
    group
  -- `t * c₁ * t⁻¹ = (t * s) ^ 4`.
  have ht_conj : t * c₁ * t⁻¹ = (t * s) ^ 4 := by
    rw [hc₁def, ← conj_pow_expand t (s * t) 4]
    congr 1
    group
  -- `s * (t * s) ^ 4 * s⁻¹ = c₁`.
  have hs_conj' : s * (t * s) ^ 4 * s⁻¹ = c₁ := by
    rw [← conj_pow_expand s (t * s) 4, hc₁def]
    congr 1
    group
  -- `t * (t * s) ^ 4 * t⁻¹ = c₁` (conjugation by `t` is an involution on the abelian `C`).
  have ht_conj' : t * (t * s) ^ 4 * t⁻¹ = c₁ := by
    have key : t * (t * c₁ * t⁻¹) * t⁻¹ = c₁ := by
      rw [show t * (t * c₁ * t⁻¹) * t⁻¹ = t * t * c₁ * (t * t)⁻¹ by group]
      rw [hCab (t * t) ht2 c₁ hc₁]
      group
    rw [← ht_conj]
    exact key
  -- The element `d = c₁ * (t * s) ^ 4 ∈ C` is fixed by conjugation by both `s` and `t`.
  have hsd : s * (c₁ * (t * s) ^ 4) * s⁻¹ = c₁ * (t * s) ^ 4 := by
    rw [show s * (c₁ * (t * s) ^ 4) * s⁻¹
        = (s * c₁ * s⁻¹) * (s * (t * s) ^ 4 * s⁻¹) by group]
    rw [hs_conj, hs_conj']
    exact (hCab c₁ hc₁ ((t * s) ^ 4) hts4C).symm
  have htd : t * (c₁ * (t * s) ^ 4) * t⁻¹ = c₁ * (t * s) ^ 4 := by
    rw [show t * (c₁ * (t * s) ^ 4) * t⁻¹
        = (t * c₁ * t⁻¹) * (t * (t * s) ^ 4 * t⁻¹) by group]
    rw [ht_conj, ht_conj']
    exact (hCab c₁ hc₁ ((t * s) ^ 4) hts4C).symm
  have hdC : c₁ * (t * s) ^ 4 ∈ C := C.mul_mem hc₁ hts4C
  -- The constraint forces `d = 1`.
  have key : c₁ * (t * s) ^ 4 = 1 := by
    by_contra hd1
    obtain ⟨k, hkV, hkne⟩ := hdesc (c₁ * (t * s) ^ 4) hdC hd1
    have hsd_pow :
        s * (c₁ * (t * s) ^ 4) ^ 2 ^ k * s⁻¹ = (c₁ * (t * s) ^ 4) ^ 2 ^ k := by
      rw [← conj_pow_expand s (c₁ * (t * s) ^ 4) (2 ^ k), hsd]
    have htd_pow :
        t * (c₁ * (t * s) ^ 4) ^ 2 ^ k * t⁻¹ = (c₁ * (t * s) ^ 4) ^ 2 ^ k := by
      rw [← conj_pow_expand t (c₁ * (t * s) ^ 4) (2 ^ k), htd]
    have h0 : (c₁ * (t * s) ^ 4) ^ 2 ^ k = v₀ := by
      rcases hfix _ hkV hsd_pow htd_pow with h | h
      · exact absurd h hkne
      · exact h
    rcases k with _ | j
    · -- `k = 0`: then `d = v₀`, contradicting the constraint at `c = c₁`.
      have hd0 : c₁ * (t * s) ^ 4 = v₀ := by simpa using h0
      refine hconstraint ⟨c₁, hc₁, ?_⟩
      rw [hs_conj, ← hCab c₁ hc₁ ((t * s) ^ 4) hts4C, hd0, hs2]
    · -- `k = j + 1`: take `c = d ^ 2 ^ j`, fixed by `s`, with square `v₀`.
      have h0' : (c₁ * (t * s) ^ 4) ^ 2 ^ (j + 1) = v₀ := h0
      refine hconstraint ⟨(c₁ * (t * s) ^ 4) ^ 2 ^ j, C.pow_mem hdC _, ?_⟩
      have hsdj :
          s * (c₁ * (t * s) ^ 4) ^ 2 ^ j * s⁻¹ = (c₁ * (t * s) ^ 4) ^ 2 ^ j := by
        rw [← conj_pow_expand s (c₁ * (t * s) ^ 4) (2 ^ j), hsd]
      rw [hsdj, ← pow_add, show 2 ^ j + 2 ^ j = 2 ^ (j + 1) by rw [pow_succ]; ring,
        h0', hs2]
  have hc1'inv : (t * s) ^ 4 = c₁⁻¹ := eq_inv_of_mul_eq_one_right key
  exact ⟨hs_conj.trans hc1'inv, ht_conj.trans hc1'inv⟩

end Work.Hering.HardCore
