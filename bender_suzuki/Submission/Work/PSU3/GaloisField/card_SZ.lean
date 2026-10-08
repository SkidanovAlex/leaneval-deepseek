/-
# The order of the Bender–Suzuki group `SZ (GF(2^(2n)))`

`SZ E = {(x,y) ∈ E² | y + y^q = x^{1+q}}` (`Work.PSU3.SZ`) is the Sylow 2-subgroup of
`PSU(3,q)`, `q = 2ⁿ`, realised as a Suzuki 2-group.  Here we compute its cardinality as

`|SZ E| = |E| · |E^σ| = 2 ^ (2n) · 2 ^ n = 2 ^ (3n)`,

where `σ = x ↦ x^q` is the distinguished involution of `E = GF(q²)`.

The proof has three ingredients.

* `card_SZ_of_trace`: in characteristic two, if the additive trace `y ↦ y + σy` maps onto the
  fixed field of `σ` (hypothesis `hTr`), then `SZ E ≃ E × E^σ`:  the fibre of the projection
  `(x,y) ↦ x` over `x` is the coset `y₀ + E^σ` of the kernel `E^σ` of the trace, because
  `x·σx` is always σ-fixed.  The bijection is explicit — with `c + σc = 1` it is
  `(x,z) ↦ (x, c·x·σx + z)` with inverse `(x,y) ↦ (x, y + c·x·σx)` — so no counting of
  fibres is needed.

* `trace_surjective_of_exists_ne_fixed`: the hypothesis `hTr` is automatic as soon as `σ ≠ 1`:
  if `σt ≠ t` then `w = t + σt` is a nonzero fixed point and `c = σt·w⁻¹` satisfies
  `c + σc = 1`, whence `y = c·z` traces to `z` for every fixed `z`.

* `exists_iterateFrobenius_ne_self`: for `n ≥ 1` the `2ⁿ`-power Frobenius of `GF(2^(2n))` is
  not the identity, since by `fixedField_card` its fixed field has `2^n < 2^(2n)` elements.

The degenerate case `n = 0` is treated separately (`card_SZ_zero`): the Frobenius is then the
identity, `2 ^ (2·0) = 1`, and `SZ E ≃ E` via the second coordinate.
-/
import Mathlib
import Submission.Work.PSU3.GaloisField
import Submission.Work.PSU3.GaloisField.fixedField_card

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.PSU3.GaloisField

open Work.PSU3

/-! ## Two elementary characteristic-two additive identities -/

section CharTwoAdd

variable {R : Type*} [Ring R] [CharP R 2]

/-- In characteristic two, `a + (b + a) = b`. -/
lemma add_add_self_left (a b : R) : a + (b + a) = b := by
  rw [add_comm b a, ← add_assoc, CharTwo.add_self_eq_zero a, zero_add]

/-- In characteristic two, `(a + b) + a = b`. -/
lemma add_self_add (a b : R) : (a + b) + a = b := by
  rw [add_comm a b, add_assoc, CharTwo.add_self_eq_zero a, add_zero]

end CharTwoAdd

/-! ## The fibre count -/

/-- **The fibre of the projection `SZ E → E` is a coset of the fixed field.**  If the additive
trace `y ↦ y + σE y` of a field `E` of characteristic two maps onto the fixed field of the
involution `σE`, then `SZ E ≃ E × E^σ` and hence `|SZ E| = |E| · |E^σ|`. -/
theorem card_SZ_of_trace (E : Type*) [Field E] [FrobeniusInvolution E] [CharP E 2]
    (hTr : ∀ z : E, σE z = z → ∃ y : E, y + σE y = z) :
    Nat.card (SZ E) = Nat.card E * Nat.card {x : E // σE x = x} := by
  classical
  obtain ⟨c, hc⟩ := hTr 1 (map_one σE)
  -- in characteristic two, a vanishing trace means a fixed point
  have hfix : ∀ w : E, w + σE w = 0 → σE w = w := fun w hw =>
    (CharTwo.add_eq_zero.mp hw).symm
  -- the trace of `y + c * (x * σx)` is zero, so it is a fixed point
  have htrace : ∀ x y : E,
      (y + c * (x * σE x)) + σE (y + c * (x * σE x)) = (y + σE y) + (c + σE c) * (x * σE x) :=
    fun x y => by
      rw [map_add, map_mul, map_mul, σE_σE]
      ring
  have e : SZ E ≃ E × {x : E // σE x = x} :=
    { toFun := fun p => (p.x, ⟨p.y + c * (p.x * σE p.x), hfix _ (by
        rw [htrace, p.herm, hc, one_mul]
        exact CharTwo.add_self_eq_zero _)⟩)
      invFun := fun q => ⟨q.1, c * (q.1 * σE q.1) + q.2.1, by
        have hz : σE q.2.1 = q.2.1 := q.2.2
        have h1 : c * (q.1 * σE q.1) + σE (c * (q.1 * σE q.1)) = q.1 * σE q.1 := by
          have step : c * (q.1 * σE q.1) + σE c * (σE q.1 * q.1)
              = (c + σE c) * (q.1 * σE q.1) := by ring
          rw [map_mul, map_mul, σE_σE, step, hc, one_mul]
        calc (c * (q.1 * σE q.1) + q.2.1) + σE (c * (q.1 * σE q.1) + q.2.1)
            = (c * (q.1 * σE q.1) + σE (c * (q.1 * σE q.1))) + (q.2.1 + σE q.2.1) := by
              rw [map_add]
              ring
          _ = q.1 * σE q.1 + 0 := by rw [h1, hz, CharTwo.add_self_eq_zero]
          _ = q.1 * σE q.1 := by rw [add_zero]⟩
      left_inv := fun p => by
        refine SZ.ext rfl ?_
        show c * (p.x * σE p.x) + (p.y + c * (p.x * σE p.x)) = p.y
        exact add_add_self_left _ _
      right_inv := fun q => by
        obtain ⟨x, z, hz⟩ := q
        refine Prod.ext rfl ?_
        refine Subtype.ext ?_
        show (c * (x * σE x) + z) + c * (x * σE x) = z
        exact add_self_add _ _ }
  calc Nat.card (SZ E) = Nat.card (E × {x : E // σE x = x}) := Nat.card_congr e
    _ = Nat.card E * Nat.card {x : E // σE x = x} := Nat.card_prod E _

/-! ## The trace is onto the fixed field -/

/-- **Trace surjectivity.**  If the involution `σE` of a field of characteristic two is not the
identity, then `y ↦ y + σE y` maps onto its fixed field: with `w = t + σt ≠ 0` (for `σt ≠ t`)
the element `(z·w⁻¹)·t` traces to `z` for every fixed `z`. -/
theorem trace_surjective_of_exists_ne_fixed (E : Type*) [Field E] [FrobeniusInvolution E]
    [CharP E 2] (h : ∃ t : E, σE t ≠ t) :
    ∀ z : E, σE z = z → ∃ y : E, y + σE y = z := by
  obtain ⟨t, ht⟩ := h
  have hw : t + σE t ≠ 0 := by
    intro h0
    exact ht (CharTwo.add_eq_zero.mp h0).symm
  have hwfix : σE (t + σE t) = t + σE t := by
    rw [map_add, σE_σE, add_comm]
  intro z hz
  refine ⟨(z * (t + σE t)⁻¹) * t, ?_⟩
  rw [map_mul, map_mul, hz, map_inv₀, hwfix, ← mul_add, mul_assoc, inv_mul_cancel₀ hw, mul_one]

/-! ## The Frobenius of `GF(2^(2n))` is not the identity for `n ≥ 1` -/

/-- For `n ≥ 1` the `2ⁿ`-power Frobenius of `GF(2^(2n))` is not the identity: its fixed field
has only `2^n < 2^(2n)` elements (`fixedField_card`). -/
theorem exists_iterateFrobenius_ne_self (n : ℕ) (hn : 1 ≤ n) :
    ∃ t : GaloisField 2 (2 * n), iterateFrobenius (GaloisField 2 (2 * n)) 2 n t ≠ t := by
  by_contra h
  simp only [not_exists, not_not] at h
  have hfix : Nat.card {x : GaloisField 2 (2 * n) //
      iterateFrobenius (GaloisField 2 (2 * n)) 2 n x = x} = 2 ^ n := fixedField_card n hn
  have hE : Nat.card (GaloisField 2 (2 * n)) = 2 ^ (2 * n) :=
    GaloisField.card 2 (2 * n) (by omega)
  have hsame : Nat.card {x : GaloisField 2 (2 * n) //
      iterateFrobenius (GaloisField 2 (2 * n)) 2 n x = x}
      = Nat.card (GaloisField 2 (2 * n)) := by
    have hsub : {x : GaloisField 2 (2 * n) |
        iterateFrobenius (GaloisField 2 (2 * n)) 2 n x = x} = Set.univ := by
      ext x
      simp [h x]
    calc Nat.card {x : GaloisField 2 (2 * n) //
          iterateFrobenius (GaloisField 2 (2 * n)) 2 n x = x}
        = Set.ncard {x : GaloisField 2 (2 * n) |
            iterateFrobenius (GaloisField 2 (2 * n)) 2 n x = x} := Nat.card_coe_set_eq _
      _ = Set.ncard (Set.univ : Set (GaloisField 2 (2 * n))) := by rw [hsub]
      _ = Nat.card (GaloisField 2 (2 * n)) := Set.ncard_univ _
  have heq : 2 ^ n = 2 ^ (2 * n) :=
    calc 2 ^ n = Nat.card {x : GaloisField 2 (2 * n) //
          iterateFrobenius (GaloisField 2 (2 * n)) 2 n x = x} := hfix.symm
      _ = Nat.card (GaloisField 2 (2 * n)) := hsame
      _ = 2 ^ (2 * n) := hE
  have h1 : n = 2 * n := Nat.pow_right_injective (by norm_num : 1 < (2 : ℕ)) heq
  omega

/-! ## The two cases of the final count -/

/-- The degenerate case `n = 0`: `iterateFrobenius E 2 0` is the identity, so the Hermitian
relation reads `y + y = x·x`, forcing `x = 0`; thus `SZ E ≃ E` through the second coordinate
and both sides are `1 · |E|`. -/
theorem card_SZ_zero :
    Nat.card (SZ (GaloisField 2 (2 * 0))) =
      2 ^ (2 * 0) * Nat.card {x : GaloisField 2 (2 * 0) //
        iterateFrobenius (GaloisField 2 (2 * 0)) 2 0 x = x} := by
  have h1 : Nat.card (SZ (GaloisField 2 (2 * 0))) = Nat.card (GaloisField 2 (2 * 0)) := by
    refine Nat.card_congr ?_
    exact
      { toFun := fun p => p.y
        invFun := fun y => ⟨0, y, by
          show y + iterateFrobenius (GaloisField 2 (2 * 0)) 2 0 y = 0 * σE 0
          simp [iterateFrobenius_zero, CharTwo.add_self_eq_zero]⟩
        left_inv := fun p => by
          have hx : p.x = 0 := by
            have h := p.herm
            have hpx : σE p.x = p.x := by
              show iterateFrobenius (GaloisField 2 (2 * 0)) 2 0 p.x = p.x
              simp [iterateFrobenius_zero]
            have hpy : σE p.y = p.y := by
              show iterateFrobenius (GaloisField 2 (2 * 0)) 2 0 p.y = p.y
              simp [iterateFrobenius_zero]
            rw [hpx, hpy] at h
            rw [CharTwo.add_self_eq_zero] at h
            exact mul_self_eq_zero.mp h.symm
          exact SZ.ext hx.symm rfl
        right_inv := fun y => rfl }
  have h2 : Nat.card {x : GaloisField 2 (2 * 0) //
        iterateFrobenius (GaloisField 2 (2 * 0)) 2 0 x = x}
      = Nat.card (GaloisField 2 (2 * 0)) := by
    simp [iterateFrobenius_zero]
  rw [h1, h2]
  simp

/-- The case `n = k + 1 ≥ 1`: `SZ E ≃ E × E^σ` by `card_SZ_of_trace`, the trace hypothesis
coming from `trace_surjective_of_exists_ne_fixed` and `exists_iterateFrobenius_ne_self`, and
`|E| = 2 ^ (2n)` by `GaloisField.card`. -/
theorem card_SZ_succ (k : ℕ) :
    Nat.card (SZ (GaloisField 2 (2 * (k + 1)))) =
      2 ^ (2 * (k + 1)) * Nat.card {x : GaloisField 2 (2 * (k + 1)) //
        iterateFrobenius (GaloisField 2 (2 * (k + 1))) 2 (k + 1) x = x} := by
  have htr : ∀ z : GaloisField 2 (2 * (k + 1)), σE z = z → ∃ y, y + σE y = z :=
    trace_surjective_of_exists_ne_fixed _
      (exists_iterateFrobenius_ne_self (k + 1) (by omega))
  have hsub : Nat.card {x : GaloisField 2 (2 * (k + 1)) // σE x = x} =
      Nat.card {x : GaloisField 2 (2 * (k + 1)) //
        iterateFrobenius (GaloisField 2 (2 * (k + 1))) 2 (k + 1) x = x} := rfl
  rw [card_SZ_of_trace _ htr, GaloisField.card 2 (2 * (k + 1)) (by omega : 2 * (k + 1) ≠ 0),
    hsub]

/-- **The cardinality of the Suzuki group `SZ (GF(2^(2n)))`**:  it is `2 ^ (2n)` times the
number of elements fixed by the `2ⁿ`-power Frobenius (i.e. `2 ^ (3n)`). -/
theorem card_SZ (n : ℕ) :
    Nat.card (SZ (GaloisField 2 (2 * n))) =
      2 ^ (2 * n) * Nat.card {x : GaloisField 2 (2 * n) //
        iterateFrobenius (GaloisField 2 (2 * n)) 2 n x = x} := by
  rcases n with _ | k
  · exact card_SZ_zero
  · exact card_SZ_succ k

end Work.PSU3.GaloisField
