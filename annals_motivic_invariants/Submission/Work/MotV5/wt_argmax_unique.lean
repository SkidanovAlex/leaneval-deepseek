import Mathlib
import Submission.Work.MotV5.WtDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted leading term of `polyOf y` has a unique maximum

`wt v g c l = (v g)^l * (v c)^5` is the weight of the monomial `c T^l` with respect to the
`5`-adic weight attached to `g` (`Submission/Work/MotV5/WtDefs.lean`).  The purpose of this file
is the following rigidity statement: if the value `v g` of `g` is **not** a fifth power of a
value (the hypothesis `hg`), then among the five monomials of `∑_{j<5} y_j T^j` with `y ≠ 0`
there is exactly one of maximal weight.

The mathematical content is completely contained in the value group.  Writing `γ = v g` and
`ω_l = v (y l)`, the weight of the `l`-th monomial is `γ^l ω_l^5`; if two nonzero monomials
`l < m` had the same weight, then

  `γ^(m-l) = (v (y l / y m))^5`,

and since `0 < m - l < 5` is invertible modulo `5`, Bezout gives
`γ = (ω^a γ^(-b))^5` for a suitable exponent pair `a d = 1 + 5 b`, so `γ` *is* a fifth power of
a value, contradicting `hg`.  The only role of `CharP F 5` is to fix the number `5` of
monomials (the argument uses only `5` and coprimality of `d < 5`; the characteristic of `F`
itself is irrelevant here).

## Contents

* `pow_five_div_of_pow_eq` — the exponent-bookkeeping identity `(ω^a / γ^b)^5 = γ` of a value
  group, valid as soon as `a * d = 1 + 5 * b` and `γ^d = ω^5` with `γ ≠ 0`;
* `exists_fifth_pow_of_pow_eq` — hence, if `γ^d = ω^5` with `1 ≤ d ≤ 4` and `γ, ω` are values
  of nonzero elements, then `γ` is itself a fifth power of a value;
* `wt_argmax_unique` — the target statement.
-/

set_option autoImplicit false

namespace Work.MotV5

/-- Exponent bookkeeping in a `LinearOrderedCommGroupWithZero`: if `a * d = 1 + 5 * b` and
`γ ^ d = ω ^ 5`, then `ω ^ a / γ ^ b` is a fifth root of `γ` (for `γ ≠ 0`).  This is Bezout's
identity `5 b ≡ -1 (mod d)` written multiplicatively. -/
lemma pow_five_div_of_pow_eq {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {γ ω : Γ₀}
    (hγ : γ ≠ 0) {d a b : ℕ} (ha : a * d = 1 + 5 * b) (h : γ ^ d = ω ^ 5) :
    (ω ^ a / γ ^ b) ^ 5 = γ := by
  have hω : ω ^ (5 * a) = γ * γ ^ (5 * b) := by
    rw [pow_mul, ← h, ← pow_mul, mul_comm d a, ha, pow_add, pow_one]
  rw [div_pow, ← pow_mul, ← pow_mul, mul_comm a 5, mul_comm b 5, hω, mul_div_assoc,
    div_self (pow_ne_zero _ hγ), mul_one]

/-- If `(v g) ^ d = (v u) ^ 5` for some `1 ≤ d ≤ 4` and `v g ≠ 0`, then `v g` is a fifth power
of a value.  The witness is `u ^ (d ^ 3) / g ^ ((d ^ 4 - 1) / 5)`: `d ^ 3` is the inverse of `d`
modulo `5`, and `d ^ 4 ≡ 1 (mod 5)` for `1 ≤ d ≤ 4`. -/
lemma exists_fifth_pow_of_pow_eq {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation F Γ₀) {g u : F} {d : ℕ} (hd1 : 1 ≤ d) (hd4 : d ≤ 4)
    (hg0 : v g ≠ 0) (h : (v g) ^ d = (v u) ^ 5) :
    ∃ u' : F, v g = (v u') ^ 5 := by
  have ha : d ^ 3 * d = 1 + 5 * ((d ^ 4 - 1) / 5) := by
    interval_cases d <;> norm_num
  refine ⟨u ^ (d ^ 3) / g ^ ((d ^ 4 - 1) / 5), ?_⟩
  rw [Valuation.map_div, Valuation.map_pow, Valuation.map_pow]
  exact (pow_five_div_of_pow_eq hg0 ha h).symm

theorem wt_argmax_unique {F Γ₀ : Type*} [Field F] [CharP F 5]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) {g : F}
    (hg : ¬ ∃ u : F, v g = (v u) ^ 5) {y : Fin 5 → F} (hy : y ≠ 0) :
    ∃! l : Fin 5, ∀ l' : Fin 5, wt v g (y l') l' ≤ wt v g (y l) l := by
  -- `g` is nonzero, since `v 0 = 0 = (v 0) ^ 5`; hence `v g ≠ 0`.
  have hgn : g ≠ 0 := by
    rintro rfl
    exact hg ⟨0, by simp [Valuation.map_zero, zero_pow (by norm_num : (5 : ℕ) ≠ 0)]⟩
  have hvgn : v g ≠ 0 := (Valuation.ne_zero_iff v).mpr hgn
  -- An index at which all weights are `≤` its weight must have `y l ≠ 0`, else all weights
  -- are `0` and hence all `y l' = 0`.
  have key_zero : ∀ l : Fin 5,
      (∀ l' : Fin 5, wt v g (y l') l' ≤ wt v g (y l) l) → y l ≠ 0 := by
    intro l hl hyl
    have hall : ∀ l' : Fin 5, y l' = 0 := by
      intro l'
      have h1 : wt v g (y l) l = 0 := by rw [hyl]; simp [wt]
      have h2 : wt v g (y l') l' ≤ 0 := h1 ▸ hl l'
      have h3 : 0 ≤ wt v g (y l') l' := zero_le
      have h4 : wt v g (y l') l' = 0 := le_antisymm h2 h3
      have h5 : (v (y l')) ^ 5 = 0 := by
        have h4' := h4
        rw [wt] at h4'
        exact (mul_eq_zero.mp h4').resolve_left (pow_ne_zero _ hvgn)
      have h6 : v (y l') = 0 := (pow_eq_zero_iff (by norm_num : (5 : ℕ) ≠ 0)).mp h5
      exact (Valuation.zero_iff v).mp h6
    exact hy (funext fun l' => hall l')
  -- Two nonzero monomials of indices `l < m` cannot have the same weight: that would exhibit
  -- `v g` as a fifth power of a value.
  have key_step : ∀ l m : Fin 5, (l : ℕ) < (m : ℕ) → y l ≠ 0 → y m ≠ 0 →
      wt v g (y l) l = wt v g (y m) m → ∃ u' : F, v g = (v u') ^ 5 := by
    intro l m hlt hyl hym heq
    have hl5 : (l : ℕ) < 5 := l.isLt
    have hm5 : (m : ℕ) < 5 := m.isLt
    set d : ℕ := (m : ℕ) - (l : ℕ) with hd
    have hm_eq : (m : ℕ) = (l : ℕ) + d := by omega
    have hd1 : 1 ≤ d := by omega
    have hd4 : d ≤ 4 := by omega
    -- Cancel `(v g) ^ l` from the equality of weights.
    have hA : (v (y l)) ^ 5 = (v g) ^ d * (v (y m)) ^ 5 := by
      have hcancel : (v g) ^ (l : ℕ) * (v (y l)) ^ 5
          = (v g) ^ (l : ℕ) * ((v g) ^ d * (v (y m)) ^ 5) := by
        calc (v g) ^ (l : ℕ) * (v (y l)) ^ 5
            = wt v g (y l) l := by rw [wt]
          _ = wt v g (y m) m := heq
          _ = (v g) ^ (m : ℕ) * (v (y m)) ^ 5 := by rw [wt]
          _ = (v g) ^ ((l : ℕ) + d) * (v (y m)) ^ 5 := by rw [hm_eq]
          _ = ((v g) ^ (l : ℕ) * (v g) ^ d) * (v (y m)) ^ 5 := by rw [pow_add]
          _ = (v g) ^ (l : ℕ) * ((v g) ^ d * (v (y m)) ^ 5) := by rw [mul_assoc]
      exact mul_left_cancel₀ (pow_ne_zero _ hvgn) hcancel
    have hB : (v (y m)) ^ 5 ≠ 0 := pow_ne_zero _ ((Valuation.ne_zero_iff v).mpr hym)
    have h1 : (v g) ^ d = (v (y l)) ^ 5 / (v (y m)) ^ 5 := by
      rw [eq_div_iff hB]
      exact hA.symm
    have hvud : (v g) ^ d = (v (y l / y m)) ^ 5 := by
      rw [h1, ← div_pow, ← Valuation.map_div]
    exact exists_fifth_pow_of_pow_eq v hd1 hd4 hvgn hvud
  have key_inj : ∀ l m : Fin 5, y l ≠ 0 → y m ≠ 0 → l ≠ m →
      wt v g (y l) l ≠ wt v g (y m) m := by
    intro l m hyl hym hne heq
    have hlm : (l : ℕ) ≠ (m : ℕ) := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hlm with hlt | hgt
    · exact hg (key_step l m hlt hyl hym heq)
    · exact hg (key_step m l hgt hym hyl heq.symm)
  -- Existence of a maximiser for the weight, and uniqueness by `key_inj`/`key_zero`.
  obtain ⟨l₀, -, hl₀⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 5))
      (fun l => wt v g (y l) l) Finset.univ_nonempty
  have hl₀' : ∀ l' : Fin 5, wt v g (y l') l' ≤ wt v g (y l₀) l₀ :=
    fun l' => hl₀ l' (Finset.mem_univ l')
  refine ⟨l₀, hl₀', ?_⟩
  intro m hm
  have hml : wt v g (y m) m = wt v g (y l₀) l₀ := le_antisymm (hl₀' m) (hm l₀)
  by_contra hne
  exact key_inj l₀ m (key_zero l₀ hl₀') (key_zero m hm) (Ne.symm hne) hml.symm

end Work.MotV5
