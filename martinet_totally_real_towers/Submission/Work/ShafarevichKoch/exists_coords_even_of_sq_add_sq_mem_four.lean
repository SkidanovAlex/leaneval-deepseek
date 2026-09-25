import Mathlib
import Submission.Work.ClassFieldTower.int_coords_and_norm
import Submission.Work.ClassFieldTower.WitnessField

/-!
# Parity of the `(1, √-30030)`-coordinates of `a` when `a² + a'² = 4c`

Let `Kc = ℚ(√-30030)` and `𝓞 Kc = ℤ[√-30030]` (the latter is
`Work.ClassFieldTower.int_coords_and_norm`).  An element `a : 𝓞 Kc` has a unique expression
`a = u + v·√-30030` with `u v : ℤ`; this file computes that, if `a² + a'²` is divisible by `4`
in `𝓞 Kc`, then

* `u` and `u'` are even, and
* `v` and `v'` have the same parity.

The mechanism is a four-squares congruence modulo `4`.  Writing `a = u + v·sc`,
`a' = u' + v'·sc` and using `sc² = -30030 ≡ 2 (mod 4)`, the identity `a² + a'² = 4c` has the two
coordinate consequences

`u² + u'² - 30030·(v² + v'²) = 4c₀`,   `2·(u·v + u'·v') = 4c₁`,

where `c = c₀ + c₁·sc`.  The first says `u² + u'² + 2·(v² + v'²) ≡ 0 (mod 4)`, the second says
`u·v + u'·v'` is even.  A finite check in `ZMod 4` then shows that necessarily `u ≡ u' ≡ 0` and
`v ≡ v' (mod 2)`: the only other solution of the first congruence modulo `4` is `u, u'` odd
(which forces `v, v'` of opposite parity, hence `u·v + u'·v'` odd), and that is excluded by the
second.

The result is used in the Shafarevich--Koch analysis of the maximal unramified pro-`2` extension
of `Kc`, where one studies the elements of `𝓞 Kc` whose square sum is `4` times an integral
element (`Kc` is imaginary quadratic with `𝓞 Kc = ℤ[√-30030]`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

/-! ## The finite congruence lemma in `ZMod 4` -/

/-- **The finite `ZMod 4` core.**  If `u² + u'² + 2(v² + v'²) = 0` and `2(uv + u'v') = 0` in
`ZMod 4`, then `u` and `u'` are `0` or `2` and `v - v'` is `0` or `2` — i.e. `u, u'` are even
and `v ≡ v' (mod 2)`.  (A `256`-case check.) -/
private lemma zmod4_parity (u u' v v' : ZMod 4)
    (h1 : u ^ 2 + u' ^ 2 + 2 * (v ^ 2 + v' ^ 2) = 0)
    (h2 : 2 * (u * v + u' * v') = 0) :
    (u = 0 ∨ u = 2) ∧ (u' = 0 ∨ u' = 2) ∧ (v - v' = 0 ∨ v - v' = 2) := by
  revert u u' v v'
  decide

/-- `0` or `2` modulo `4` means even. -/
private lemma even_of_zmod4 {x : ℤ} (h : (x : ZMod 4) = 0 ∨ (x : ZMod 4) = 2) : Even x := by
  have h2 : (2 : ℤ) ∣ x := by
    rcases h with h | h
    · exact dvd_trans (by norm_num : (2 : ℤ) ∣ 4) ((ZMod.intCast_zmod_eq_zero_iff_dvd x 4).mp h)
    · have h4 : (4 : ℤ) ∣ x - 2 := by
        refine (ZMod.intCast_zmod_eq_zero_iff_dvd (x - 2) 4).mp ?_
        push_cast
        rw [h]
        simp
      obtain ⟨k, hk⟩ := dvd_trans (by norm_num : (2 : ℤ) ∣ 4) h4
      exact ⟨k + 1, by omega⟩
  exact even_iff_two_dvd.mpr h2

/-- **The integer parity lemma.**  If `4 ∣ u² + u'² - 30030·(v² + v'²)` and `u·v + u'·v'` is
even then `u, u'` are even and `v - v'` is even (so also `v + v'` is even).

`30030 ≡ 2 (mod 4)` turns the first divisibility into `u² + u'² + 2(v² + v'²) ≡ 0 (mod 4)`,
which together with `uv + u'v' ≡ 0 (mod 2)` is exactly the finite core `zmod4_parity`. -/
private lemma parity_of_four_dvd_sq_add_aux {u u' v v' : ℤ}
    (h1 : (4 : ℤ) ∣ u ^ 2 + u' ^ 2 - 30030 * (v ^ 2 + v' ^ 2))
    (h2 : (2 : ℤ) ∣ u * v + u' * v') :
    Even u ∧ Even u' ∧ (2 : ℤ) ∣ v + v' ∧ (2 : ℤ) ∣ v - v' := by
  -- `30030 = 2 + 4·7508`, so the first congruence becomes `u² + u'² + 2(v² + v'²) ≡ 0 (mod 4)`.
  have h1' : (4 : ℤ) ∣ u ^ 2 + u' ^ 2 + 2 * (v ^ 2 + v' ^ 2) := by
    obtain ⟨k, hk⟩ := h1
    exact ⟨k + 7508 * (v ^ 2 + v' ^ 2), by linear_combination hk⟩
  have h2' : (4 : ℤ) ∣ 2 * (u * v + u' * v') := by
    obtain ⟨m, hm⟩ := h2
    exact ⟨m, by rw [hm]; ring⟩
  -- Pass to `ZMod 4`.
  have h1z : ((u : ZMod 4)) ^ 2 + ((u' : ZMod 4)) ^ 2
      + 2 * (((v : ZMod 4)) ^ 2 + ((v' : ZMod 4)) ^ 2) = 0 := by
    have h : (((u ^ 2 + u' ^ 2 + 2 * (v ^ 2 + v' ^ 2) : ℤ)) : ZMod 4) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr h1'
    push_cast at h
    simpa using h
  have h2z : (2 * (((u : ZMod 4)) * ((v : ZMod 4))
      + ((u' : ZMod 4)) * ((v' : ZMod 4))) : ZMod 4) = 0 := by
    have h : (((2 * (u * v + u' * v') : ℤ)) : ZMod 4) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr h2'
    push_cast at h
    simpa using h
  obtain ⟨hu, hu', hv⟩ := zmod4_parity _ _ _ _ h1z h2z
  have hvv : Even (v - v') := by
    refine even_of_zmod4 ?_
    simpa only [Int.cast_sub] using hv
  obtain ⟨k, hk⟩ := hvv
  exact ⟨even_of_zmod4 hu, even_of_zmod4 hu', ⟨k + v', by omega⟩, ⟨k, by omega⟩⟩

/-! ## Coordinates in `ℚ(√-30030)` -/

/-- **The coordinates of a square.**  In `Kc = ℚ(√-30030)`, with `sc = √-30030` and
`sc² = -30030`,

`(p + q·sc)² = (p² - 30030 q²) + (2 p q)·sc`. -/
private lemma sq_coords (p q : ℤ) :
    (((p : Kc)) + ((q : Kc)) * sc) ^ 2
      = ((p ^ 2 - 30030 * q ^ 2 : ℤ) : Kc) + ((2 * p * q : ℤ) : Kc) * sc := by
  have hsq : (((p : Kc)) + ((q : Kc)) * sc) ^ 2
      = (p : Kc) ^ 2 + 2 * (p : Kc) * (q : Kc) * sc + (q : Kc) ^ 2 * (sc * sc) := by ring
  rw [hsq, sc_sq_num]
  push_cast
  ring

/-- **The coordinates are unique.**  If `p + q·sc = r + s·sc` in `Kc` with `p q r s : ℤ`, then
`p = r` and `q = s`; this is the linear independence of `{1, sc}` over `ℚ`. -/
private lemma coords_unique {p q r s : ℤ}
    (h : (p : Kc) + (q : Kc) * sc = (r : Kc) + (s : Kc) * sc) : p = r ∧ q = s := by
  have hcast : ∀ n : ℤ, ((n : Kc)) = algebraMap ℚ Kc ((n : ℚ)) := by intro n; norm_num
  have h'' := h
  rw [hcast p, hcast q, hcast r, hcast s] at h''
  have h3 : algebraMap ℚ Kc ((p - r : ℚ)) + algebraMap ℚ Kc ((q - s : ℚ)) * sc = 0 := by
    rw [map_sub, map_sub]
    linear_combination h''
  have hsmul : ((p - r : ℚ)) • (1 : Kc) + ((q - s : ℚ)) • sc = 0 := by
    simpa only [Algebra.smul_def, mul_one] using h3
  have hlin := (LinearIndependent.pair_iff (x := (1 : Kc)) (y := sc)).mp
    Work.ClassFieldTower.linearIndependent_pair_one_sc
  obtain ⟨hP, hQ⟩ := hlin ((p - r : ℚ)) ((q - s : ℚ)) hsmul
  exact ⟨Int.cast_injective (sub_eq_zero.mp hP), Int.cast_injective (sub_eq_zero.mp hQ)⟩

/-- **Coordinates with evenness.**  If `a` has coordinates `u + v·sc` and `4 ∣ a² + a'²` in
`𝓞 Kc`, then `u` and `u'` are even and `v ≡ v' (mod 2)`. -/
private lemma coords_parity_of_four_dvd {a a' : NumberField.RingOfIntegers Kc} {u v u' v' c₀ c₁ : ℤ}
    (huv : (a : Kc) = (u : Kc) + (v : Kc) * sc)
    (hu'v' : (a' : Kc) = (u' : Kc) + (v' : Kc) * sc)
    (h4 : (a : Kc) ^ 2 + (a' : Kc) ^ 2
      = ((4 * c₀ : ℤ) : Kc) + ((4 * c₁ : ℤ) : Kc) * sc) :
    Even u ∧ Even u' ∧ (2 : ℤ) ∣ v + v' ∧ (2 : ℤ) ∣ v - v' := by
  have hmain : (a : Kc) ^ 2 + (a' : Kc) ^ 2
      = ((u ^ 2 + u' ^ 2 - 30030 * (v ^ 2 + v' ^ 2) : ℤ) : Kc)
        + ((2 * (u * v + u' * v') : ℤ) : Kc) * sc := by
    rw [huv, hu'v', sq_coords u v, sq_coords u' v']
    push_cast
    ring
  have key := coords_unique (hmain.symm.trans h4)
  have h2eq : 2 * (u * v + u' * v') = 4 * c₁ := key.2
  exact parity_of_four_dvd_sq_add_aux ⟨c₀, key.1⟩ ⟨c₁, by omega⟩

/-- **Even coordinates of `a`, `a'` when `a² + a'² = 4c`.**

If `a² + a'²` is divisible by `4` in `𝓞 ℚ(√-30030)`, then the coordinates `(u, v)`, `(u', v')`
of `a`, `a'` in the `ℤ`-basis `{1, √-30030}` of `𝓞 ℚ(√-30030)` satisfy: `u` and `u'` are even,
and `v`, `v'` have the same parity (`2 ∣ v + v'` and `2 ∣ v - v'`). -/
theorem exists_coords_even_of_sq_add_sq_mem_four (a a' : NumberField.RingOfIntegers Work.ClassFieldTower.Kc)
    (h : ∃ c : NumberField.RingOfIntegers Work.ClassFieldTower.Kc, a ^ 2 + a' ^ 2 = 4 * c) :
    ∃ u v u' v' : ℤ,
      (a : Work.ClassFieldTower.Kc) = (u : Work.ClassFieldTower.Kc)
          + (v : Work.ClassFieldTower.Kc) * Work.ClassFieldTower.sc ∧
      (a' : Work.ClassFieldTower.Kc) = (u' : Work.ClassFieldTower.Kc)
          + (v' : Work.ClassFieldTower.Kc) * Work.ClassFieldTower.sc ∧
      Even u ∧ Even u' ∧ (2 : ℤ) ∣ v + v' ∧ (2 : ℤ) ∣ v - v' := by
  obtain ⟨u, v, huv, _⟩ := Work.ClassFieldTower.int_coords_and_norm a
  obtain ⟨u', v', hu'v', _⟩ := Work.ClassFieldTower.int_coords_and_norm a'
  obtain ⟨c, hca⟩ := h
  obtain ⟨c₀, c₁, hcc, _⟩ := Work.ClassFieldTower.int_coords_and_norm c
  -- Coordinates of `4·c`.
  have hcast4 : (((4 * c : NumberField.RingOfIntegers Kc)) : Kc)
      = ((4 * c₀ : ℤ) : Kc) + ((4 * c₁ : ℤ) : Kc) * sc := by
    have h1 : (((4 * c : NumberField.RingOfIntegers Kc)) : Kc) = 4 * (c : Kc) := by
      simp only [map_mul, map_ofNat]
    rw [h1, hcc]
    push_cast
    ring
  have h4 : (a : Kc) ^ 2 + (a' : Kc) ^ 2
      = ((4 * c₀ : ℤ) : Kc) + ((4 * c₁ : ℤ) : Kc) * sc := by
    rw [← hcast4]
    have hcast := congrArg (fun z : NumberField.RingOfIntegers Kc => (z : Kc)) hca
    push_cast at hcast
    exact hcast
  obtain ⟨hu, hu', hvsum, hvdiff⟩ := coords_parity_of_four_dvd huv hu'v' h4
  exact ⟨u, v, u', v', huv, hu'v', hu, hu', hvsum, hvdiff⟩

end Work.ShafarevichKoch
