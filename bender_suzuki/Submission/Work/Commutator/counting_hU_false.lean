import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

namespace Work.Commutator

/-- Pure finite-field endgame of the two-cover exclusion: the hypotheses are inconsistent.

Mathematical sketch (characteristic 2, `F` a finite field with `|F| = 2^n`, `n ≥ 2`).

Expanding `hU` at the point `u + u'` and using additivity of `d`, `b` in the first
variable together with the Frobenius additivity `(x+y)^(2^k) = x^(2^k) + y^(2^k)`
(valid in characteristic 2) yields the cross relation
`d u * (b u' v)^(2^k) = d u' * (b u v)^(2^k)` for all `u u' v`.
Multiplying by the `hU`-relations and cancelling `c0` gives the bilinear-rank-one form
`(d u)^2 * b u' v = (d u')^2 * b u v`, hence `b u v = (d u)^2 * c v` for the single
function `c v = b 1 v / (d 1)^2`.

Since `b(·,v)` is non-degenerate on the right (`hdv`), `c` vanishes only at `0`, so on the
finite field `c` is injective and hence surjective.  Therefore for each `u ≠ 0` the image
`{(d u)^2 * c v : v} = F` is everything: choosing `v` with `b u v = 1` and applying `hU`
gives `d u = c0`.  Thus `d` is constant `c0 ≠ 0` on `F^*`, while additivity forces
`d(u + u') = d u + d u' = c0 + c0 = 0` for two distinct non-zero `u, u'` — contradiction
(here `|F| ≥ 4` is used to find two distinct non-zero elements). -/
theorem counting_hU_false {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    {n k : ℕ} (hn : 2 ≤ n) (hcard : Fintype.card F = 2 ^ n)
    (c0 : F) (hc0 : c0 ≠ 0) (b : F → F → F)
    (hb1 : ∀ u u' v : F, b (u + u') v = b u v + b u' v)
    (hb2 : ∀ u v v' : F, b u (v + v') = b u v + b u v')
    (d : F → F) (hdadd : ∀ u u' : F, d (u + u') = d u + d u')
    (hdu : ∀ u : F, u ≠ 0 → ∃ v : F, b u v ≠ 0)
    (hdv : ∀ v : F, v ≠ 0 → ∃ u : F, b u v ≠ 0)
    (hU : ∀ u v : F, d u * (b u v) ^ (2 ^ k) = c0 * b u v) :
    False := by
  -- In characteristic `2`, `a = a + a` forces `a = 0`.
  have eq0 : ∀ {a : F}, a = a + a → a = 0 := by
    intro a h
    have h2 : a + 0 = a + a := by rw [add_zero]; exact h
    exact (add_left_cancel h2).symm
  have hd0 : d 0 = 0 := eq0 (by simpa using hdadd 0 0)
  have hb0 : ∀ v : F, b 0 v = 0 := fun v => eq0 (by simpa using hb1 0 0 v)
  -- The cross relation obtained by expanding `hU` at `u + u'`.
  have key : ∀ u u' v : F, (d u)^2 * b u' v = (d u')^2 * b u v := by
    intro u u' v
    have hcross : d u * (b u' v) ^ (2 ^ k) = d u' * (b u v) ^ (2 ^ k) := by
      have h := hU (u + u') v
      rw [hdadd, hb1] at h
      rw [add_pow_char_pow] at h
      have h1 := hU u v
      have h2 := hU u' v
      rw [mul_add, add_mul, add_mul] at h
      rw [h1, h2, mul_add] at h
      have hsum : d u' * (b u v) ^ (2^k) + d u * (b u' v) ^ (2^k) = 0 := by
        linear_combination h
      have := neg_eq_of_add_eq_zero_left hsum
      rw [CharTwo.neg_eq] at this
      exact this
    apply mul_left_cancel₀ hc0
    calc c0 * ((d u)^2 * b u' v)
        = (d u)^2 * (c0 * b u' v) := by ring
      _ = (d u)^2 * (d u' * (b u' v)^(2 ^ k)) := by rw [← hU u' v]
      _ = (d u * d u') * (d u * (b u' v)^(2 ^ k)) := by ring
      _ = (d u * d u') * (d u' * (b u v)^(2 ^ k)) := by rw [hcross]
      _ = (d u')^2 * (d u * (b u v)^(2 ^ k)) := by ring
      _ = (d u')^2 * (c0 * b u v) := by rw [hU u v]
      _ = c0 * ((d u')^2 * b u v) := by ring
  -- `d` never vanishes on a non-zero argument.
  have hd_ne : ∀ u : F, u ≠ 0 → d u ≠ 0 := by
    intro u hu h
    obtain ⟨v, hv⟩ := hdu u hu
    have h1 := hU u v
    rw [h, zero_mul] at h1
    exact hv ((mul_eq_zero.mp h1.symm).resolve_left hc0)
  -- The single function `c` with `b u v = (d u)^2 * c v`.
  let c : F → F := fun v => b 1 v / (d 1)^2
  have hb_eq : ∀ u v : F, b u v = (d u)^2 * c v := by
    intro u v
    have hk : (d 1)^2 * b u v = (d u)^2 * b 1 v := (key u 1 v).symm
    have hdd1 : (d 1)^2 ≠ 0 := pow_ne_zero 2 (hd_ne 1 one_ne_zero)
    dsimp only [c]
    rw [← mul_div_assoc, eq_div_iff hdd1]
    rw [mul_comm (b u v) ((d 1)^2)]
    exact hk
  have hcadd : ∀ v v' : F, c (v + v') = c v + c v' := by
    intro v v'
    dsimp only [c]
    rw [hb2 1 v v', add_div]
  have hc_ne : ∀ v : F, v ≠ 0 → c v ≠ 0 := by
    intro v hv h0
    obtain ⟨u, hu⟩ := hdv v hv
    have h1 := hb_eq u v
    rw [h1, h0, mul_zero] at hu
    exact hu rfl
  have hc_inj : Function.Injective c := by
    intro v v' hvv
    have hz : c (v + v') = 0 := by
      rw [hcadd, hvv, CharTwo.add_self_eq_zero]
    have hv0 : v + v' = 0 := by
      by_contra h
      exact hc_ne (v + v') h hz
    have hv0' : v' + v = 0 := by rw [add_comm]; exact hv0
    have h : v' = -v := eq_neg_of_add_eq_zero_left hv0'
    rw [h, CharTwo.neg_eq]
  have hc_surj : Function.Surjective c :=
    Finite.injective_iff_surjective.mp hc_inj
  -- `d` is constant `c0` on non-zero arguments.
  have hd_const : ∀ u : F, u ≠ 0 → d u = c0 := by
    intro u hu
    have hdun : d u ≠ 0 := hd_ne u hu
    obtain ⟨v, hv⟩ := hc_surj ((d u)^2)⁻¹
    have h1 : b u v = 1 := by
      rw [hb_eq u v, hv, mul_inv_cancel₀ (pow_ne_zero 2 hdun)]
    have h2 := hU u v
    rw [h1] at h2
    simpa using h2
  -- Two distinct non-zero elements exist, since `|F| = 2^n ≥ 4`.
  have hcard_lt : ({0, 1} : Finset F).card < (Finset.univ : Finset F).card := by
    rw [Finset.card_pair (zero_ne_one : (0:F) ≠ 1), Finset.card_univ, hcard]
    simpa using Nat.pow_lt_pow_right (show 1 < 2 by norm_num) (show 1 < n by omega)
  obtain ⟨e, _, he⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard_lt
  have he' : e ≠ 0 ∧ e ≠ 1 := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using he
  obtain ⟨he0, he1⟩ := he'
  have huu : e + 1 ≠ 0 := by
    intro h
    apply he1
    have : e = -1 := eq_neg_of_add_eq_zero_left h
    rw [this, CharTwo.neg_eq]
  -- Additivity of `d` at `e + 1` now forces `c0 + c0 = c0`, i.e. `c0 = 0`.
  have h1 : d (e + 1) = c0 := hd_const (e + 1) huu
  rw [hdadd, hd_const e he0, hd_const 1 one_ne_zero] at h1
  exact hc0 (eq0 h1.symm)

end Work.Commutator
