import Mathlib
import Submission.Work.Drive.OrderBase
import Submission.Work.Drive.OrderAlgebra
import Submission.Work.Drive.OrderRelation
import Submission.Work.Drive.parityCore_of_stripRel

/-!
# The final assembly of `ParityCore γ` from a side function with the functional identity

`Work.Drive.chainParity` (equivalently `Work.Drive.parityCore_of_isSmoothEmbedding`,
`Work.Drive.stripRel_exists`) is the geometric core: the existence of the mod-2 order function
`b : Zc γ → ZMod 2`.  The chain route produces it as the "side" function

> `b u = #{C₀ ⋔ A_u}  (mod 2)`,   `A_u = P ∩ V_u`  the cut of an essential loop `C₀ = ℝP¹`

of Hugelmeyer's ordering, and proves about it the three identities

* **local constancy** — the count is a mod-2 intersection number of transverse chains, hence constant
  in a neighbourhood of every `u ∈ Zc γ`;
* **antisymmetry** (Hugelmeyer's Lemma 3) — `b u + b (-u) = 1` for `u ∈ Zc γ`;
* **multiplicativity plus the triple identity** (Hugelmeyer's Lemma 4, `(SURF)`) — for
  `a, c, a + c ∈ Zc γ`, the three triple counts of the triple of rotated planes
  `(0, a, a+c)` (all of whose pairwise differences lie in `Zc γ`) are the three products
  `b a · b (a+c)`, `b (-a) · b c`, `b (-(a+c)) · b (-c)`, and their *sum* is `1` (Lemma 4).

This file records the last mile: these three identities already force `ParityCore γ`, through the
pure `ZMod 2` lemma `Work.Drive.e_add_of_triple` (`OrderAlgebra.lean`).  Nothing geometric is added
here; the content is the exact interface the counting half has to hit.

## The functional identity

The identity

> `b a · b (a + c) + b (-a) · b c + b (-(a + c)) · b (-c) = 1`   (`a, c, a + c ∈ Zc γ`)

is *not* a further geometric input: it is Hugelmeyer's Lemma 4 read on the triple
`(P_0, P_a, P_{a+c})` with the multiplicativity `n_P = b (v - u) · b (w - u)` of `(SURF)`
(`SWEEP_TRANSPORT_NOTES.md` §3, `Surf/ChainForm.lean`).  With `a = v - u` and `c = w - v` its three
terms are exactly `n_{P_u}, n_{P_v}, n_{P_w}`.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

/-- **`ParityCore γ` from a side function with the functional identity.**

If `e : Zc γ → ZMod 2` is continuous (equivalently, locally constant — the openness clause of the
order), antisymmetric, and satisfies the functional identity of Hugelmeyer's Lemma 4, then
`e` is the required order function and `ParityCore γ` holds.  The proof is
`Work.Drive.e_add_of_triple`: antisymmetry at `a` and at `c` turns the two cross terms of the
functional identity into `0`, leaving `e (a + c) = 1`. -/
theorem parityCore_of_functional {γ : Circle → ℝ × ℝ}
    (e : Zc γ → ZMod 2) (he : Continuous e)
    (hanti : ∀ (u : UnitAddCircle) (hu : u ∈ Zc γ),
      e ⟨u, hu⟩ + e ⟨-u, neg_mem_Zc hu⟩ = 1)
    (hT : ∀ (a : UnitAddCircle) (ha : a ∈ Zc γ) (c : UnitAddCircle) (hc : c ∈ Zc γ)
      (hac : a + c ∈ Zc γ),
      e ⟨a, ha⟩ * e ⟨a + c, hac⟩ + e ⟨-a, neg_mem_Zc ha⟩ * e ⟨c, hc⟩
        + e ⟨-(a + c), neg_mem_Zc hac⟩ * e ⟨-c, neg_mem_Zc hc⟩ = 1) :
    ParityCore γ := by
  refine ⟨e, he, hanti, ?_⟩
  intro a ha c hc ha1 hc1 hac
  -- antisymmetry kills the two cross terms of the functional identity
  have hna : e ⟨-a, neg_mem_Zc ha⟩ = 0 := by
    have h := hanti a ha
    rw [ha1] at h
    exact (add_left_inj (1 : ZMod 2)).mp (by simpa using h)
  have hnc : e ⟨-c, neg_mem_Zc hc⟩ = 0 := by
    have h := hanti c hc
    rw [hc1] at h
    exact (add_left_inj (1 : ZMod 2)).mp (by simpa using h)
  have h := hT a ha c hc hac
  rw [ha1, hna, hnc] at h
  simpa using h

/-- **The same assembly, with the functional identity supplied through a triple count.**

Often the geometry produces, instead of `hT` directly, a three-variable count
`n u v w` (the number of essential-loop intersections of the triple of rotated planes with rotation
parameters `u, v, w`), together with *multiplicativity*
`n u v w = e (v - u) · e (w - u)` and the *triple identity* `n u v w + n v w u + n w u v = 1`
(Hugelmeyer's Lemma 4).  With `u = 0`, `v = a`, `w = a + c` these give the functional identity of
`parityCore_of_functional`. -/
theorem parityCore_of_threeCount {γ : Circle → ℝ × ℝ}
    (e : Zc γ → ZMod 2) (he : Continuous e)
    (hanti : ∀ (u : UnitAddCircle) (hu : u ∈ Zc γ),
      e ⟨u, hu⟩ + e ⟨-u, neg_mem_Zc hu⟩ = 1)
    (n : UnitAddCircle → UnitAddCircle → UnitAddCircle → ZMod 2)
    (hn : ∀ (a : UnitAddCircle) (ha : a ∈ Zc γ) (c : UnitAddCircle) (hc : c ∈ Zc γ)
      (hac : a + c ∈ Zc γ),
      n 0 a (a + c) + n a (a + c) 0 + n (a + c) 0 a = 1)
    (hmul0 : ∀ (a : UnitAddCircle) (ha : a ∈ Zc γ) (c : UnitAddCircle) (hc : c ∈ Zc γ)
      (hac : a + c ∈ Zc γ),
      n 0 a (a + c) = e ⟨a, ha⟩ * e ⟨a + c, hac⟩)
    (hmul1 : ∀ (a : UnitAddCircle) (ha : a ∈ Zc γ) (c : UnitAddCircle) (hc : c ∈ Zc γ)
      (hac : a + c ∈ Zc γ),
      n a (a + c) 0 = e ⟨-a, neg_mem_Zc ha⟩ * e ⟨c, hc⟩)
    (hmul2 : ∀ (a : UnitAddCircle) (ha : a ∈ Zc γ) (c : UnitAddCircle) (hc : c ∈ Zc γ)
      (hac : a + c ∈ Zc γ),
      n (a + c) 0 a = e ⟨-(a + c), neg_mem_Zc hac⟩ * e ⟨-c, neg_mem_Zc hc⟩) :
    ParityCore γ :=
  parityCore_of_functional e he hanti fun a ha c hc hac => by
    have h := hn a ha c hc hac
    rw [hmul0 a ha c hc hac, hmul1 a ha c hc hac, hmul2 a ha c hc hac] at h
    exact h

/-- **The parity of a natural sum, read in `ZMod 2`.**  `Odd (a + b + c)` is exactly
`((a : ZMod 2) + b + c) = 1` — the bridge from the engine's `Odd`-valued conclusions
(`Work.Drive.odd_sum_topBdryMeet_clampedSweeps_of_planes`) to the `ZMod 2` form of the functional
identity. -/
lemma zmod2_eq_one_of_odd (a b c : ℕ) (h : Odd (a + b + c)) :
    ((a : ZMod 2) + b + c) = 1 := by
  have hcast : ((a + b + c : ℕ) : ZMod 2) = (a : ZMod 2) + b + c := by push_cast; ring
  rw [← hcast]
  exact ZMod.natCast_eq_one_iff_odd.mpr h

/-- **`ParityCore γ` from the engine's own output.**  This is `parityCore_of_threeCount` with the
triple identity in the exact shape the counting engine produces it: the three counts are natural
numbers (the `ncard`s of the three top faces) whose sum is `Odd`
(`Work.Drive.odd_sum_topBdryMeet_clampedSweeps_of_planes`), and the multiplicativity
(`n_P ≡ ε_Q ε_R`, Hugelmeyer's Lemma 2 + `(SURF)`) is the statement that their casts to `ZMod 2` are
the products of the two side values.  -/
theorem parityCore_of_oddThreeCount {γ : Circle → ℝ × ℝ}
    (e : Zc γ → ZMod 2) (he : Continuous e)
    (hanti : ∀ (u : UnitAddCircle) (hu : u ∈ Zc γ),
      e ⟨u, hu⟩ + e ⟨-u, neg_mem_Zc hu⟩ = 1)
    (n : UnitAddCircle → UnitAddCircle → UnitAddCircle → ℕ)
    (hn : ∀ (a : UnitAddCircle) (ha : a ∈ Zc γ) (c : UnitAddCircle) (hc : c ∈ Zc γ)
      (hac : a + c ∈ Zc γ),
      Odd (n 0 a (a + c) + n a (a + c) 0 + n (a + c) 0 a))
    (hmul0 : ∀ (a : UnitAddCircle) (ha : a ∈ Zc γ) (c : UnitAddCircle) (hc : c ∈ Zc γ)
      (hac : a + c ∈ Zc γ),
      ((n 0 a (a + c) : ℕ) : ZMod 2) = e ⟨a, ha⟩ * e ⟨a + c, hac⟩)
    (hmul1 : ∀ (a : UnitAddCircle) (ha : a ∈ Zc γ) (c : UnitAddCircle) (hc : c ∈ Zc γ)
      (hac : a + c ∈ Zc γ),
      ((n a (a + c) 0 : ℕ) : ZMod 2) = e ⟨-a, neg_mem_Zc ha⟩ * e ⟨c, hc⟩)
    (hmul2 : ∀ (a : UnitAddCircle) (ha : a ∈ Zc γ) (c : UnitAddCircle) (hc : c ∈ Zc γ)
      (hac : a + c ∈ Zc γ),
      ((n (a + c) 0 a : ℕ) : ZMod 2) = e ⟨-(a + c), neg_mem_Zc hac⟩ * e ⟨-c, neg_mem_Zc hc⟩) :
    ParityCore γ :=
  parityCore_of_functional e he hanti fun a ha c hc hac => by
    have h := zmod2_eq_one_of_odd (n 0 a (a + c)) (n a (a + c) 0) (n (a + c) 0 a)
      (hn a ha c hc hac)
    rwa [hmul0 a ha c hc hac, hmul1 a ha c hc hac, hmul2 a ha c hc hac] at h


/-- Every element of `ZMod 2` is `0` or `1`. -/
private lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> first | exact Or.inl rfl | exact Or.inr rfl

/-! ## The functional-identity form of the side function

The three properties which the geometry produces about `e` are packaged below as `HasFunctional`; the
`iff` at the end of this file shows that they are *exactly* `ParityCore γ`: no property of `e` is lost
and none is added. -/

/-- The three properties of the side function produced by the counting route: local constancy,
antisymmetry, and the functional identity of Hugelmeyer's Lemma 4 (multiplicativity `(SURF)` plus the
triple count). -/
def HasFunctional (γ : Circle → ℝ × ℝ) (e : Zc γ → ZMod 2) : Prop :=
  Continuous e ∧
  (∀ (u : UnitAddCircle) (hu : u ∈ Zc γ), e ⟨u, hu⟩ + e ⟨-u, neg_mem_Zc hu⟩ = 1) ∧
  (∀ (a : UnitAddCircle) (ha : a ∈ Zc γ) (c : UnitAddCircle) (hc : c ∈ Zc γ)
    (hac : a + c ∈ Zc γ),
    e ⟨a, ha⟩ * e ⟨a + c, hac⟩ + e ⟨-a, neg_mem_Zc ha⟩ * e ⟨c, hc⟩
      + e ⟨-(a + c), neg_mem_Zc hac⟩ * e ⟨-c, neg_mem_Zc hc⟩ = 1)

/-- `ParityCore γ` from a functional-identity side function. -/
theorem parityCore_of_hasFunctional {γ : Circle → ℝ × ℝ} {e : Zc γ → ZMod 2}
    (h : HasFunctional γ e) : ParityCore γ :=
  parityCore_of_functional e h.1 h.2.1 h.2.2

/-- **The functional identity is exactly the transitivity clause.**  A `ParityCore` side function
always satisfies the functional identity: transitivity settles the case in which the two cross terms
vanish (applied to the negated angles, using antisymmetry), and in the remaining cases the identity is
pure `ZMod 2` arithmetic.  Hence `ParityCore γ` and `∃ e, HasFunctional γ e` are equivalent, and the
counting route's hypothesis list is *sharp*. -/
theorem hasFunctional_of_parityCore {γ : Circle → ℝ × ℝ} (h : ParityCore γ) :
    ∃ e : Zc γ → ZMod 2, HasFunctional γ e := by
  obtain ⟨b, hcont, hanti, htrans⟩ := h
  refine ⟨b, hcont, hanti, ?_⟩
  intro a ha c hc hac
  rcases zmod2_cases (b ⟨a, ha⟩) with hx | hx <;>
    rcases zmod2_cases (b ⟨c, hc⟩) with hy | hy
  · -- `b a = 0`, `b c = 0`: transitivity of the negated angles forces `b (a+c) = 0`
    have hna1 : b ⟨-a, neg_mem_Zc ha⟩ = 1 := by
      have hh := hanti a ha
      rw [hx, zero_add] at hh
      exact hh
    have hnc1 : b ⟨-c, neg_mem_Zc hc⟩ = 1 := by
      have hh := hanti c hc
      rw [hy, zero_add] at hh
      exact hh
    have hsum : (-a) + (-c) = -(a + c) := by abel
    have hac' : (-a) + (-c) ∈ Zc γ := by rw [hsum]; exact neg_mem_Zc hac
    have hb' : b ⟨-(a + c), neg_mem_Zc hac⟩ = 1 := by
      have h := htrans (-a) (neg_mem_Zc ha) (-c) (neg_mem_Zc hc) hna1 hnc1 hac'
      rwa [show (⟨(-a) + (-c), hac'⟩ : Zc γ) = ⟨-(a + c), neg_mem_Zc hac⟩ from
        Subtype.ext hsum] at h
    have hz0 : b ⟨a + c, hac⟩ = 0 := by
      have hh := hanti (a + c) hac
      rw [hb'] at hh
      exact (add_right_inj (1 : ZMod 2)).mp (by simpa using hh)
    rw [hx, hy, hz0, hna1, hnc1, hb']
    ring
  · -- `b a = 0`, `b c = 1`
    have hna1 : b ⟨-a, neg_mem_Zc ha⟩ = 1 := by
      have hh := hanti a ha
      rw [hx, zero_add] at hh
      exact hh
    have hnc0 : b ⟨-c, neg_mem_Zc hc⟩ = 0 := by
      have hh := hanti c hc
      rw [hy] at hh
      exact (add_left_inj (1 : ZMod 2)).mp (by simpa using hh)
    rw [hx, hy, hna1, hnc0]
    ring
  · -- `b a = 1`, `b c = 0`
    have hna0 : b ⟨-a, neg_mem_Zc ha⟩ = 0 := by
      have hh := hanti a ha
      rw [hx] at hh
      exact (add_left_inj (1 : ZMod 2)).mp (by simpa using hh)
    have hnc1 : b ⟨-c, neg_mem_Zc hc⟩ = 1 := by
      have hh := hanti c hc
      rw [hy, zero_add] at hh
      exact hh
    rcases zmod2_cases (b ⟨a + c, hac⟩) with hz | hz
    · have hb' : b ⟨-(a + c), neg_mem_Zc hac⟩ = 1 := by
        have hh := hanti (a + c) hac
        rw [hz, zero_add] at hh
        exact hh
      rw [hx, hy, hz, hna0, hnc1, hb']
      ring
    · have hb' : b ⟨-(a + c), neg_mem_Zc hac⟩ = 0 := by
        have hh := hanti (a + c) hac
        rw [hz] at hh
        exact (add_left_inj (1 : ZMod 2)).mp (by simpa using hh)
      rw [hx, hy, hz, hna0, hnc1, hb']
      ring
  · -- `b a = 1`, `b c = 1`: transitivity gives `b (a+c) = 1`
    have hna0 : b ⟨-a, neg_mem_Zc ha⟩ = 0 := by
      have hh := hanti a ha
      rw [hx] at hh
      exact (add_left_inj (1 : ZMod 2)).mp (by simpa using hh)
    have hnc0 : b ⟨-c, neg_mem_Zc hc⟩ = 0 := by
      have hh := hanti c hc
      rw [hy] at hh
      exact (add_left_inj (1 : ZMod 2)).mp (by simpa using hh)
    have hz1 : b ⟨a + c, hac⟩ = 1 := htrans a ha c hc hx hy hac
    have hb' : b ⟨-(a + c), neg_mem_Zc hac⟩ = 0 := by
      have hh := hanti (a + c) hac
      rw [hz1] at hh
      exact (add_left_inj (1 : ZMod 2)).mp (by simpa using hh)
    rw [hx, hy, hz1, hna0, hnc0, hb']
    ring

/-- **The exact interface of the counting route.**  `ParityCore γ` holds if and only if there is a
side function `e : Zc γ → ZMod 2` which is locally constant, antisymmetric, and satisfies the
functional identity of Hugelmeyer's Lemma 4. -/
theorem parityCore_iff_hasFunctional {γ : Circle → ℝ × ℝ} :
    ParityCore γ ↔ ∃ e : Zc γ → ZMod 2, HasFunctional γ e :=
  ⟨hasFunctional_of_parityCore, fun h => by
    rcases h with ⟨e, he⟩
    exact parityCore_of_hasFunctional he⟩



/-- **Multiplicativity of parities, in `ZMod 2` form.**  `(SURF)` produces the parity statement
`Odd #(A ⋔ B) ↔ (Odd ⟨A,L⟩ ∧ Odd ⟨B,L⟩)` (`Work.Drive.surf_intersection_form_line*`), while the
functional identity of the order is a *product* in `ZMod 2`; this lemma is the bridge. -/
lemma cast_eq_mul_of_iff_odd (x y z : ℕ) (h : Odd x ↔ (Odd y ∧ Odd z)) :
    (x : ZMod 2) = (y : ZMod 2) * z := by
  have hy0 : ¬ Odd y → (y : ZMod 2) = 0 := fun hny => by
    by_contra hne
    exact hny (ZMod.natCast_ne_zero_iff_odd.mp hne)
  have hz0 : ¬ Odd z → (z : ZMod 2) = 0 := fun hnz => by
    by_contra hne
    exact hnz (ZMod.natCast_ne_zero_iff_odd.mp hne)
  rcases zmod2_cases (x : ZMod 2) with hx | hx
  · rw [hx]
    have hnx : ¬ Odd x := by
      intro hox
      rw [ZMod.natCast_eq_one_iff_odd.mpr hox] at hx
      exact zero_ne_one hx.symm
    have hnyz : ¬ (Odd y ∧ Odd z) := fun hc => hnx (h.mpr hc)
    rcases not_and_or.mp hnyz with hny | hnz
    · rw [hy0 hny, zero_mul]
    · rw [hz0 hnz, mul_zero]
  · rw [hx]
    obtain ⟨hy, hz⟩ := h.mp (ZMod.natCast_eq_one_iff_odd.mp hx)
    rw [ZMod.natCast_eq_one_iff_odd.mpr hy, ZMod.natCast_eq_one_iff_odd.mpr hz, mul_one]

/-- **`StripRel γ Rel` from a two-variable count.**  The lead's formulation of the geometric core is
`∃ Rel, StripRel γ Rel` (`OrderRelation.lean`), with `Rel u v` meaning `u·M ≺ v·M`.  The chain route
produces, for each pair `(u, v)` with `v - u ∈ Zc γ`, the mod-2 *pair count*

> `n u v = #{essential loop of P_u ⋔ V_v}  (mod 2)`

(`SWEEP_TRANSPORT_NOTES.md` §3).  This theorem records that the four clauses of `StripRel` are exactly
the four properties the count has to satisfy:

* `hn1` — **rotation invariance of the count**, `n u v = n 0 (v - u)` (the equivariance
  `Work.Drive.topBdryMeet_rotCapping_clampedSweep`);
* `hn2` — **antisymmetry** (Hugelmeyer's Lemma 3), `n u v + n v u = 1` on disjoint pairs;
* `hn3` — **the triple identity with multiplicativity** (Hugelmeyer's Lemma 4 + `(SURF)`), i.e. the
  functional identity of `parityCore_of_functional` for `e u := n 0 u`;
* `hn4` — **local constancy** of the count (it is a mod-2 intersection number of transverse chains;
  `Work.Drive.locallyConstant_labelMeet_eq`).

Clause 1 of `StripRel` is the two-valuedness of `n` together with `hn2`, clause 2 is `hn1`, clause 3
is `hn3` with the antisymmetry (exactly as in `parityCore_of_functional`), and clause 4 is `hn4`. -/
theorem stripRel_of_count {γ : Circle → ℝ × ℝ}
    (n : UnitAddCircle → UnitAddCircle → ZMod 2)
    (hn1 : ∀ u v : UnitAddCircle, n u v = n 0 (v - u))
    (hn2 : ∀ u v : UnitAddCircle, v - u ∈ Zc γ → n u v + n v u = 1)
    (hn3 : ∀ (a : UnitAddCircle) (ha : a ∈ Zc γ) (c : UnitAddCircle) (hc : c ∈ Zc γ)
      (hac : a + c ∈ Zc γ),
      n 0 a * n 0 (a + c) + n 0 (-a) * n 0 c + n 0 (-(a + c)) * n 0 (-c) = 1)
    (hn4 : Continuous (fun p : UnitAddCircle × UnitAddCircle => n p.1 p.2)) :
    ∃ Rel : UnitAddCircle → UnitAddCircle → Prop, StripRel γ Rel := by
  refine ⟨fun u v => n u v = 1, ?_, ?_, ?_, ?_⟩
  · -- clause 1: antisymmetry
    intro u v hv
    constructor
    · intro huv hvu
      have h := hn2 u v hv
      rw [huv] at h
      have h0 : n v u = 0 := (add_left_inj (1 : ZMod 2)).mp (by simpa using h)
      rw [h0] at hvu
      exact zero_ne_one hvu
    · intro hvu
      have h := hn2 u v hv
      rcases zmod2_cases (n v u) with h0 | h1
      · simpa [h0] using h
      · exact absurd h1 hvu
  · -- clause 2: rotation invariance
    intro u v w
    show (n u v = 1) ↔ (n (u + w) (v + w) = 1)
    have hsub : (v + w) - (u + w) = v - u := by abel
    rw [hn1 (u + w) (v + w), hn1 u v, hsub]
  · -- clause 3: transitivity
    intro u v w huv hvw huw huvW hvwW
    set a : UnitAddCircle := v - u with ha_def
    set c : UnitAddCircle := w - v with hc_def
    have ha : a ∈ Zc γ := huv
    have hc : c ∈ Zc γ := hvw
    have hsum : a + c = w - u := by rw [ha_def, hc_def]; abel
    have hac : a + c ∈ Zc γ := by rw [hsum]; exact huw
    have hea : n 0 a = 1 := by rw [← hn1 u v]; exact huvW
    have hec : n 0 c = 1 := by rw [← hn1 v w]; exact hvwW
    have ha' : a - 0 ∈ Zc γ := by simpa using ha
    have hna : n 0 (-a) = 0 := by
      have h := hn2 0 a ha'
      have h1 : n a 0 = n 0 (-a) := by simpa using hn1 a 0
      rw [h1, hea] at h
      exact (add_left_inj (1 : ZMod 2)).mp (by simpa using h)
    have hc' : c - 0 ∈ Zc γ := by simpa using hc
    have hnc : n 0 (-c) = 0 := by
      have h := hn2 0 c hc'
      have h1 : n c 0 = n 0 (-c) := by simpa using hn1 c 0
      rw [h1, hec] at h
      exact (add_left_inj (1 : ZMod 2)).mp (by simpa using h)
    have h3 := hn3 a ha c hc hac
    have hkey : n 0 (a + c) = 1 := by
      rw [hea, hna, hec, hnc] at h3
      simpa using h3
    show n u w = 1
    rw [hn1 u w]
    rwa [← hsum]
  · -- clause 4: openness from local constancy
    intro u v _ huvW
    have hopen : IsOpen ((fun p : UnitAddCircle × UnitAddCircle => n p.1 p.2) ⁻¹' {n u v}) :=
      hn4.isOpen_preimage {n u v} (isOpen_discrete {n u v})
    have hmem : (u, v) ∈ (fun p : UnitAddCircle × UnitAddCircle => n p.1 p.2) ⁻¹' {n u v} := by
      simp [huvW]
    obtain ⟨U, V, hUo, hVo, huU, hvV, hUV⟩ := (isOpen_prod_iff.mp hopen) u v hmem
    exact ⟨U, V, hUo, hVo, huU, hvV, fun u' hu' v' hv' _ => by
      have h1 : n u' v' = n u v := by
        have hmem' : (u', v') ∈ U ×ˢ V := ⟨hu', hv'⟩
        have := hUV hmem'
        simpa using this
      show n u' v' = 1
      rw [h1]; exact huvW⟩


/-- **`ParityCore γ` directly from the two-variable count** — `stripRel_of_count` composed with
`Work.Drive.parityCore_of_stripRel`.  This is the shortest path from the counting route's output to
the wall. -/
theorem parityCore_of_count {γ : Circle → ℝ × ℝ}
    (n : UnitAddCircle → UnitAddCircle → ZMod 2)
    (hn1 : ∀ u v : UnitAddCircle, n u v = n 0 (v - u))
    (hn2 : ∀ u v : UnitAddCircle, v - u ∈ Zc γ → n u v + n v u = 1)
    (hn3 : ∀ (a : UnitAddCircle) (ha : a ∈ Zc γ) (c : UnitAddCircle) (hc : c ∈ Zc γ)
      (hac : a + c ∈ Zc γ),
      n 0 a * n 0 (a + c) + n 0 (-a) * n 0 c + n 0 (-(a + c)) * n 0 (-c) = 1)
    (hn4 : Continuous (fun p : UnitAddCircle × UnitAddCircle => n p.1 p.2)) :
    ParityCore γ :=
  (stripRel_of_count n hn1 hn2 hn3 hn4).elim (fun _ hRel => parityCore_of_stripRel hRel)

end Work.Drive
