import Mathlib
import Submission.Work.ORLyndon.twoOccBase

/-!
# The order of the two-occurrence ratio is infinite

Let `u ∈ F(α)` be a cyclically reduced relator which is not a proper power, let `x ∈ α` be a letter
of `u`, and suppose that the two occurrences of `x^{±1}` in `u` are exhibited by a decomposition

`u = P · xb · A · xb · B`   (`xb = x` for `b = true`, `xb = x⁻¹` for `b = false`),

with `P, A, B` in the Magnus subgroup `F(α ∖ {x})` (this is exactly the shape in which the
`x`-component of the Fox vector of `u` has *two* terms, see `Work.ORLyndon.rootVec_eq_of_twoOcc`).

The lemma proved here is the **order certificate** of that situation:

> the class of the ratio `twoOccRatio x b A` in `⟨α | u ^ l⟩` — the ratio of the two occurrence
> terms of `∂u/∂x` — has **infinite order**, for every `l : ℕ`.

Equivalently (`Work.ORLyndon.annAt_of_two_monomials_of_eq_sign`) the two-term component
`rootVec K (u ^ l) u x = (unit) · (1 + of (ratio))` is a non-zero-divisor.  The statement is
exactly the residual left open in `NOTES_epsNeZeroDescent_level.md` §9.3–§9.6 ("the two-term case is
exactly an order statement"): the Freiheitssatz certificate cannot be applied to the ratio itself
(neither it nor its complement misses a letter of `u`), but — this is the trick below — it *can* be
applied to the **square** of the ratio, which is the class of a word in the other letters.

## The proof

It is the elementary trick recorded in the block comment of `Work.ORLyndon.epsNeZeroDescent`:

* In `Q = ⟨α | u⟩` the relation `P · xb · A · xb · B = 1` gives `xb · A · xb = P⁻¹ · B⁻¹`, hence (by
  a pure group identity, `sq_eq_of_mul_eq_one`) `(xb · A)² = P⁻¹ B⁻¹ A`;
* `P⁻¹ B⁻¹ A = 1` in the free group would give `A = B P`, hence `u = (P · xb · B)²`, a proper power
  — so `P⁻¹B⁻¹A` is a **nontrivial** element of the free Magnus subgroup `F(α ∖ {x})`
  (`twoOcc_ne_one_of_not_isProperPower`);
* by the Freiheitssatz (`Work.ORLyndon.orderOf_presentedGroupMap_misses_eq_zero`) that element has
  **infinite** order in `Q`; the square of the ratio being equal to it, the ratio has infinite order
  in `Q` as well (`orderOf_eq_zero_of_pow_eq_zero`);
* finally `⟨α | u ^ l⟩ ↠ ⟨α | u⟩` (because `⟨⟨u ^ l⟩⟩ ≤ ⟨⟨u⟩⟩`, for *every* `l`, including `l = 0`),
  and infinite order is inherited from an image (`orderOf_eq_zero_of_map_eq_zero`).

Note the `b = false` case: `u = P · x⁻¹ · A · x⁻¹ · B` gives `(A · x⁻¹)² = A P⁻¹ B⁻¹`, and
`A P⁻¹ B⁻¹ = 1` again forces `A = BP`.  Both cases are covered, uniformly in `l`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORLyndon

/-! ## Two elementary group lemmas -/

section General

/-- **The square identity.**  If `p * y * a * y * q = 1` in a group, then `(y * a) ^ 2 = p⁻¹ q⁻¹ a`:
the relation `y * a * y = p⁻¹ * q⁻¹` is the "cyclic permutation" of the given one. -/
theorem sq_eq_of_mul_eq_one {G : Type*} [Group G] {p y a q : G} (h : p * y * a * y * q = 1) :
    (y * a) ^ 2 = p⁻¹ * q⁻¹ * a := by
  have hyay : y * a * y = p⁻¹ * q⁻¹ := by
    have h1 : p⁻¹ * (p * y * a * y * q) * q⁻¹ = p⁻¹ * q⁻¹ := by rw [h, mul_one]
    rwa [show p⁻¹ * (p * y * a * y * q) * q⁻¹ = y * a * y from by group] at h1
  calc (y * a) ^ 2 = (y * a * y) * a := by simp only [pow_two, mul_assoc]
    _ = p⁻¹ * q⁻¹ * a := by rw [hyay]

/-- The companion of `sq_eq_of_mul_eq_one` with `a` and `y` interchanged:
`(a * y) ^ 2 = a * (p⁻¹ * q⁻¹)`. -/
theorem sq_eq_of_mul_eq_one' {G : Type*} [Group G] {p y a q : G} (h : p * y * a * y * q = 1) :
    (a * y) ^ 2 = a * (p⁻¹ * q⁻¹) := by
  have hyay : y * a * y = p⁻¹ * q⁻¹ := by
    have h1 : p⁻¹ * (p * y * a * y * q) * q⁻¹ = p⁻¹ * q⁻¹ := by rw [h, mul_one]
    rwa [show p⁻¹ * (p * y * a * y * q) * q⁻¹ = y * a * y from by group] at h1
  calc (a * y) ^ 2 = a * (y * a * y) := by simp only [pow_two, mul_assoc]
    _ = a * (p⁻¹ * q⁻¹) := by rw [hyay]

/-- Infinite order is inherited from a non-zero power: if `g ^ n` has infinite order and `n ≠ 0`,
then so has `g`. -/
theorem orderOf_eq_zero_of_pow_eq_zero {G : Type*} [Group G] {g : G} {n : ℕ} (hn : n ≠ 0)
    (h : orderOf (g ^ n) = 0) : orderOf g = 0 := by
  rw [orderOf_eq_zero_iff'] at h ⊢
  intro m hm hm1
  exact h m hm (by rw [← pow_mul', pow_mul, hm1, one_pow])

/-- Infinite order is inherited from an image: if `ψ g` has infinite order then so has `g`
(the order of an image divides the order of the element). -/
theorem orderOf_eq_zero_of_map_eq_zero {G H : Type*} [Group G] [Group H] (ψ : G →* H) {g : G}
    (h : orderOf (ψ g) = 0) : orderOf g = 0 := by
  have hdvd : orderOf (ψ g) ∣ orderOf g := orderOf_map_dvd ψ g
  rw [h] at hdvd
  exact Nat.eq_zero_of_zero_dvd hdvd

end General

/-! ## The two-occurrence lemmas -/

section TwoOccNoDecEq

variable {α : Type*} {u : FreeGroup α} {x : α} {b : Bool}
  {P A B : FreeGroup {z : α // z ≠ x}}

/-- `presentRho u ∘ magIncl x` is the canonical map `F(α ∖ {x}) →* ⟨α | u⟩` of the Magnus
subgroup; both sides send a generator of `F(α ∖ {x})` to the corresponding generator of `⟨α | u⟩`. -/
theorem presentRho_magIncl_eq_presentedGroupMap (u : FreeGroup α) (x : α)
    (W : FreeGroup {z : α // z ≠ x}) :
    presentRho u (magIncl x W) = Work.OROneRel.presentedGroupMap u {z : α | z ≠ x} W := by
  have h : Work.OROneRel.presentedGroupMap u {z : α | z ≠ x}
      = (presentRho u).comp (magIncl x) := by
    ext z
    simp [Work.OROneRel.presentedGroupMap, magIncl, presentRho]
  rw [h]
  rfl

/-- **The word of the square is nontrivial.**  If `P⁻¹ B⁻¹ A = 1` (resp. `A P⁻¹ B⁻¹ = 1`) then
`A = B P`, whence `u = (P · xb · B)²` is a proper power.  So, `u` not being a proper power, the
word whose class is the square of the ratio is nontrivial in the free group `F(α ∖ {x})` — this is
what lets the Freiheitssatz see it. -/
theorem twoOcc_ne_one_of_not_isProperPower
    (hu : u = magIncl x P * xbOf x b * magIncl x A * xbOf x b * magIncl x B)
    (hpp : ¬ Work.OROneRel.IsProperPower u) :
    (if b then P⁻¹ * B⁻¹ * A else A * P⁻¹ * B⁻¹) ≠ 1 := by
  intro hW
  apply hpp
  have hA : A = B * P := by
    rcases b with _ | _
    · simp only [Bool.false_eq_true, reduceIte] at hW
      have h1 : (A * P⁻¹ * B⁻¹) * (B * P) = 1 * (B * P) := by rw [hW]
      rwa [show (A * P⁻¹ * B⁻¹) * (B * P) = A from by group, one_mul] at h1
    · simp only [if_true] at hW
      have h1 : P * (P⁻¹ * B⁻¹ * A) = P * 1 := by rw [hW]
      have h2 : B⁻¹ * A = P := by
        rwa [show P * (P⁻¹ * B⁻¹ * A) = B⁻¹ * A from by group, mul_one] at h1
      have h3 : B * (B⁻¹ * A) = B * P := by rw [h2]
      rwa [show B * (B⁻¹ * A) = A from by group] at h3
  refine ⟨magIncl x P * xbOf x b * magIncl x B, 2, le_refl 2, ?_⟩
  rw [hu, hA]
  simp only [map_mul, pow_two, mul_assoc]

end TwoOccNoDecEq

section TwoOcc

variable {α : Type*} [DecidableEq α] {u : FreeGroup α} {x : α} {b : Bool} {l : ℕ}
  {P A B : FreeGroup {z : α // z ≠ x}}

/-- **The square of the ratio is a word in the other letters.**  With `u = P · xb · A · xb · B`, the
square of the class of the ratio `twoOccRatio x b A` in `Q = ⟨α | u⟩` is the class of the word
`P⁻¹ B⁻¹ A` (for `b = true`), resp. `A P⁻¹ B⁻¹` (for `b = false`), which lies in the Magnus subgroup
`F(α ∖ {x})`. -/
theorem twoOccRatio_sq_eq
    (hu : u = magIncl x P * xbOf x b * magIncl x A * xbOf x b * magIncl x B) :
    (presentRho u (twoOccRatio x b A)) ^ 2
      = presentRho u (if b then magIncl x (P⁻¹ * B⁻¹ * A) else magIncl x (A * P⁻¹ * B⁻¹)) := by
  have hrel : presentRho u (magIncl x P) * presentRho u (xbOf x b) * presentRho u (magIncl x A) *
      presentRho u (xbOf x b) * presentRho u (magIncl x B) = 1 := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← hu, presentRho_relator]
  rcases b with _ | _
  · have h := sq_eq_of_mul_eq_one' hrel
    simp only [twoOccRatio, xbOf, Bool.false_eq_true, reduceIte, map_mul, map_inv] at h ⊢
    rw [h, mul_assoc]
  · have h := sq_eq_of_mul_eq_one hrel
    simp only [twoOccRatio, xbOf, if_true, map_mul, map_inv] at h ⊢
    rw [h]

/-- The quotient map `⟨α | u ^ l⟩ →* ⟨α | u⟩`, induced by `⟨⟨u ^ l⟩⟩ ≤ ⟨⟨u⟩⟩`: it exists for every
`l : ℕ` (for `l = 0` it is the map `⟨α | 1⟩ →* ⟨α | u⟩`) and sends generators to generators. -/
theorem exists_hom_oneRelatorGroup_pow (u : FreeGroup α) (l : ℕ) :
    ∃ ψ : OneRelatorGroup (u ^ l) →* OneRelatorGroup u,
      ∀ m : FreeGroup α, ψ (presentRho (u ^ l) m) = presentRho u m := by
  have hlift : FreeGroup.lift (fun a : α => (PresentedGroup.of a : OneRelatorGroup u))
      = presentRho u := by
    ext a
    exact (presentRho_of u a).symm
  have hrel : ∀ r' ∈ ({u ^ l} : Set (FreeGroup α)),
      FreeGroup.lift (fun a : α => (PresentedGroup.of a : OneRelatorGroup u)) r' = 1 := by
    intro r' hr'
    rw [Set.mem_singleton_iff] at hr'
    subst hr'
    rw [hlift, map_pow, presentRho_relator, one_pow]
  refine ⟨PresentedGroup.toGroup
    (f := fun a : α => (PresentedGroup.of a : OneRelatorGroup u)) hrel, fun m => ?_⟩
  have heq : (PresentedGroup.toGroup
        (f := fun a : α => (PresentedGroup.of a : OneRelatorGroup u)) hrel).comp
        (presentRho (u ^ l)) = presentRho u := by
    ext a
    simp only [MonoidHom.comp_apply, presentRho_of, PresentedGroup.toGroup.of]
  rw [← MonoidHom.comp_apply, heq]

/-- **The order certificate for the two-occurrence ratio.**  In `⟨α | u ^ l⟩` the ratio of the two
occurrence terms of `∂u/∂x` — the element `twoOccRatio x b A` of `F(α)` — has infinite order. -/
theorem orderOf_presentRho_twoOcc {α : Type*} [DecidableEq α] {u : FreeGroup α} {x : α}
    {b : Bool} {l : ℕ} (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hpp : ¬ Work.OROneRel.IsProperPower u)
    (hx : x ∈ Work.OROneRel.relatorLetters u) {P A B : FreeGroup {z : α // z ≠ x}}
    (hu : u = Work.ORLyndon.magIncl x P * Work.ORLyndon.xbOf x b * Work.ORLyndon.magIncl x A *
      Work.ORLyndon.xbOf x b * Work.ORLyndon.magIncl x B) :
    orderOf (Work.ORLyndon.presentRho (u ^ l) (Work.ORLyndon.twoOccRatio x b A)) = 0 := by
  -- Step 1: the class of the ratio has infinite order in `Q = ⟨α | u⟩`.
  have hQ : orderOf (presentRho u (twoOccRatio x b A)) = 0 := by
    have hsq := twoOccRatio_sq_eq (u := u) (x := x) (b := b) (P := P) (A := A) (B := B) hu
    have hW := twoOcc_ne_one_of_not_isProperPower (u := u) (x := x) (b := b) (P := P) (A := A)
      (B := B) hu hpp
    rcases b with _ | _
    · have hsq' : (presentRho u (magIncl x A * (FreeGroup.of x)⁻¹)) ^ 2
          = presentRho u (magIncl x (A * P⁻¹ * B⁻¹)) := by
        simpa only [twoOccRatio, Bool.false_eq_true, reduceIte] using hsq
      have hW' : A * P⁻¹ * B⁻¹ ≠ 1 := by
        simpa only [Bool.false_eq_true, reduceIte] using hW
      simp only [twoOccRatio, Bool.false_eq_true, reduceIte]
      refine orderOf_eq_zero_of_pow_eq_zero (n := 2) (by norm_num) ?_
      rw [hsq', presentRho_magIncl_eq_presentedGroupMap]
      exact orderOf_presentedGroupMap_misses_eq_zero (u := u) hcyc (y := x) hx hW'
    · have hsq' : (presentRho u (FreeGroup.of x * magIncl x A)) ^ 2
          = presentRho u (magIncl x (P⁻¹ * B⁻¹ * A)) := by
        simpa only [twoOccRatio, if_true] using hsq
      have hW' : P⁻¹ * B⁻¹ * A ≠ 1 := by
        simpa only [if_true] using hW
      simp only [twoOccRatio, if_true]
      refine orderOf_eq_zero_of_pow_eq_zero (n := 2) (by norm_num) ?_
      rw [hsq', presentRho_magIncl_eq_presentedGroupMap]
      exact orderOf_presentedGroupMap_misses_eq_zero (u := u) hcyc (y := x) hx hW'
  -- Step 2: transport along the surjection `⟨α | u ^ l⟩ ↠ ⟨α | u⟩`.
  obtain ⟨ψ, hψ⟩ := exists_hom_oneRelatorGroup_pow (α := α) u l
  exact orderOf_eq_zero_of_map_eq_zero ψ (by rw [hψ]; exact hQ)

end TwoOcc

end Work.ORLyndon
