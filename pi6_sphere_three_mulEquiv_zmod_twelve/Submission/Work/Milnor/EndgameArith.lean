import Mathlib
import Submission.Work.Cohomology.Degree

/-!
# The arithmetic of the endgame for Milnor's exotic 7-sphere

Suppose `F : Mk (-2) ≃ₘ S⁷`.  Gluing the disc bundle `D(ξ)` of the rank-`4` bundle `ξ = ξ_{-2}`
over `S⁴` (whose unit sphere bundle is `Mk (-2)`) to `D⁸` along `F` produces a closed oriented
smooth `8`-manifold `X`.  Writing `H^4(X;ℤ) = ℤ⟨x⟩`, `H^8(X;ℤ) = ℤ⟨ω⟩`, `x ⌣ x = m ω`,
`p₁(X) = c x` (with `c = ±6`) and `σ(X)` for the signature, one has:

* `σ(X) = sign m` (the intersection form is the `1×1` form `(m)`, i.e. it is `m = ±1` by Poincaré
  duality);
* `p₁(X)² = c² m = 36 m`;
* Hirzebruch in dimension `8`: `45 σ(X) = 7 p₂(X) - p₁(X)²`.

The two numeric consequences recorded here are the two forms in which the obstruction is usually
quoted:

* the *integrality* form: with `m = ±1` the identity `45 σ = 7 p₂ - 36 m` forces `7 ∣ 81`;
* the *congruence* form: with `m = ±1` the congruence `36 m ≡ 4 σ (mod 7)` forces `m ≡ 0 (mod 7)`.

Both are impossible, so `F` cannot exist — **provided** `m = ±1` (Poincaré duality) and the
dimension-`8` Hirzebruch identity are available.

## Main results

* `endgame_arithmetic_integrality` — `45 σ = 7 p₂ - 36 m`, `m = ±1`, `σ = sign m` is impossible;
* `endgame_arithmetic_congruence` — `36 m ≡ 4 sign m (mod 7)`, `m = ±1` is impossible;
* `endgame_arithmetic` — the packaged form used in the final assembly.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Milnor

/-- **The integrality form of the endgame.**  There are no integers `m`, `p₂`, `σ` with
`m = σ = 1` or `m = σ = -1` and `45 σ = 7 p₂ - 36 m`. -/
theorem endgame_arithmetic_integrality (m p₂ σ : ℤ)
    (hm : (m = 1 ∧ σ = 1) ∨ (m = -1 ∧ σ = -1)) (h : 45 * σ = 7 * p₂ - 36 * m) : False := by
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega

/-- **The congruence form of the endgame.**  There are no integers `m`, `σ` with `m = σ = 1` or
`m = σ = -1` and `36 m ≡ 4 σ (mod 7)`. -/
theorem endgame_arithmetic_congruence (m σ : ℤ)
    (hm : (m = 1 ∧ σ = 1) ∨ (m = -1 ∧ σ = -1)) (h : 36 * m ≡ 4 * σ [ZMOD 7]) : False := by
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · norm_num at h
  · norm_num at h

/-- **The endgame, packaged.**  The dimension-`8` Hirzebruch identity `45 σ = 7 p₂ - 36 m` is
incompatible with `m = ±1` (Poincaré duality) and `σ = sign m` (the signature of the `1×1`
intersection form `(m)`). -/
theorem endgame_arithmetic (m p₂ σ : ℤ)
    (hm : (m = 1 ∧ σ = 1) ∨ (m = -1 ∧ σ = -1)) (h : 45 * σ = 7 * p₂ - 36 * m) : False :=
  endgame_arithmetic_integrality m p₂ σ hm h

/-- **The sharpened endgame (session 13).**  For the capped manifold `X = D(ξ) ∪_F D⁸` one has
`p₂(X) = 0` (both pieces have `H⁸ = 0`), `p₁(X) = ±6 x` with `x` the generator of `H⁴(X;ℤ) = ℤ`,
`x ⌣ x = m ω`, and `σ(X) = sign m` (the intersection form is the `1×1` form `(m)`).  Hirzebruch in
dimension `8` therefore reads `45 σ = -36 m`.  This file records that this equation alone (with
`σ = sign m`) forces `m = 0`.

Consequently **`m ≠ 0`** — the mere non-degeneracy of the intersection form, i.e. the crux of
`Submission/NOTES.md` §12.7 — is already incompatible with the dimension-`8` Hirzebruch identity;
the stronger input `m = ±1` (unimodularity of the intersection form) is *not* needed for the
identity (only for the congruence form).  The characterisation `σ = sign m` used here is
`σ * |m| = m`, which is vacuous at `m = 0`. -/
theorem endgame_arithmetic_sharp (m σ : ℤ) (hσ : σ * |m| = m) (h : 45 * σ = -36 * m) :
    m = 0 := by
  by_contra hm0
  have hm0' : m ≠ 0 := hm0
  have h1 : |σ| = 1 := by
    have h2 : |σ| * |m| = |m| := by
      have h3 : abs (σ * |m|) = |m| := by rw [hσ]
      simpa [abs_mul] using h3
    exact mul_right_cancel₀ (abs_ne_zero.mpr hm0') (by rw [h2, one_mul])
  have h4 : (45 : ℤ) * |σ| = 36 * |m| := by
    have h5 : abs ((45 : ℤ) * σ) = abs ((-36 : ℤ) * m) := by rw [h]
    rw [abs_mul, abs_mul] at h5
    norm_num at h5
    linarith [h5]
  rw [h1, mul_one] at h4
  omega

/-- **The sharpened endgame, packaged.**  `45 σ = -36 m` (Hirzebruch in dimension `8` for
`p₂ = 0` and `p₁² = 36 m`) together with `σ = sign m` and `m ≠ 0` is a contradiction. -/
theorem endgame_arithmetic_sharp' (m σ : ℤ) (hσ : σ * |m| = m) (h : 45 * σ = -36 * m)
    (hm : m ≠ 0) : False := by
  exact hm (endgame_arithmetic_sharp m σ hσ h)


/-- **The endgame, with the `p₂`-number assumed to vanish.**

Hirzebruch's identity in dimension `8` reads `45 σ = 7 p₂ - p₁²`.  **If** the `p₂`-number of the
closed `8`-manifold `X` vanishes, this is `45 σ = -p₁²`; writing `p₁ = c · x` for the generator `x`
of `H⁴(X; ℤ) ≅ ℤ` and `x ⌣ x = m · ω` for the fundamental class `ω` (so that the intersection form
on `H⁴(X;ℚ) = ℚ` is `m` times the standard one and `σ = sign m`), the identity becomes
`45 σ = -c² m`.  This is a pure **sign** contradiction for **every** `c` and `m ≠ 0` — in particular
the value of `p₁` is irrelevant *in this case*.

CAUTION (see `Submission/NOTES.md` §14.7): the vanishing `p₂(X) = 0` is *not* free — for
`ξ = L` the manifold `D(ξ) ∪ D⁸` is `ℍP²`, whose `p₂`-number is `7 ≠ 0`, and the data
`(c, m, σ, p₂) = (2, 1, 1, 7)` satisfies both Hirzebruch and the spin integrality
`7p₁² - 4p₂ ≡ 0 (mod 5760)`.  So this lemma does *not* by itself finish the endgame; it isolates
one of the two viable routes (the other being `m = ±1` together with `p₁(ξ) = ±6`). -/
theorem endgame_arithmetic_general (c m σ : ℤ) (hσ : σ = Int.sign m) (hm : m ≠ 0)
    (h : 45 * σ = -(c^2) * m) : False := by
  rcases lt_trichotomy m 0 with hlt | heq | hgt
  · have hs : Int.sign m = -1 := Int.sign_eq_neg_one_of_neg hlt
    rw [hσ, hs] at h
    have hnn : c^2 * m ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg c) (le_of_lt hlt)
    nlinarith
  · exact absurd heq hm
  · have hs : Int.sign m = 1 := Int.sign_eq_one_of_pos hgt
    rw [hσ, hs] at h
    have hnn : 0 ≤ c^2 * m := mul_nonneg (sq_nonneg c) (le_of_lt hgt)
    nlinarith


/-- **The endgame arithmetic on the congruence route.**  If the intersection form is unimodular
(`m = ±1`), `σ = m`, and the dimension-`8` Hirzebruch *congruence* `p₁² ≡ 4 σ (mod 7)` holds with
`p₁ = c · x` and `x ⌣ x = m · ω` (so `p₁² ≡ c² m`), then `7 ∣ c² - 4`.  So any `c` with
`c² ≢ 4 (mod 7)` — in particular `c = ±6`, as for `ξ = L²R^{-1}` — gives a contradiction. -/
theorem endgame_congruence_route (c m : ℤ) (hm : m = 1 ∨ m = -1)
    (h : 7 ∣ c^2 * m - 4 * m) : 7 ∣ c^2 - 4 := by
  rcases hm with rfl | rfl
  · simpa using h
  · have h' : 7 ∣ -(c^2 - 4) := by
      have : c^2 * (-1) - 4 * (-1) = -(c^2 - 4) := by ring
      rw [← this]; exact h
    exact dvd_neg.mp h'

/-- **The endgame on the congruence route, packaged.**  Unimodularity of the intersection form
(`m = ±1`), the identification `σ = m` of the signature with the sign of the middle
self-intersection, the Hirzebruch congruence `p₁² ≡ 4 σ (mod 7)`, and `c² ≢ 4 (mod 7)` where
`p₁ = c·x` — these are jointly contradictory.  This is the form of the endgame that uses only the
*congruence* `p₁² ≡ 4σ (mod 7)` (a consequence of the dimension-`8` Hirzebruch identity) and the
non-vanishing `p₁(ξ) ≢ ±2 (mod 7)`. -/
theorem endgame_congruence_route' (c m : ℤ) (hm : m = 1 ∨ m = -1)
    (h : 7 ∣ c^2 * m - 4 * m) (hc : ¬ (7 ∣ c^2 - 4)) : False :=
  hc (endgame_congruence_route c m hm h)

/-- `c = 6` (the value `p₁(ξ) = ±6` for Milnor's bundle) satisfies `c² ≢ 4 (mod 7)`. -/
theorem six_sq_not_dvd (c : ℤ) (hc : c = 6 ∨ c = -6) : ¬ (7 ∣ c^2 - 4) := by
  rcases hc with rfl | rfl <;> decide

end Work.Milnor
