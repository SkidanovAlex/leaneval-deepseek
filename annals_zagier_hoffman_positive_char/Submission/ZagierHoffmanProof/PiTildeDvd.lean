import Submission.ZagierHoffmanProof.TpAux

/-!
# The `π̃`-divisibility criterion, in the form Step 3(a) uses it

Dac §5.3/§6 Step 3 runs on the identity

  `π̃^m · f_𝔱(θ) = (∏_j Γ_j) · b(θ) · ambInfHom(ζ_A 𝔰)`

with `f_𝔱(θ) ∈ K = F_q(θ)` and everything on the right in the image of the completion at `∞`.  Since
`π̃^m` lies in the image of `ambInfHom` **iff** `(q-1) ∣ m`, the identity forces the dichotomy

  `(q-1) ∣ m`,   or   `f_𝔱(θ) = 0`,

and the second alternative is excluded by the induction hypothesis.  `TpAux.dvd_pred_of_piTilde_pow_mem_range`
supplies the "iff" direction; this file supplies the dichotomy by observing that the image of
`ambInfHom` is a *subfield* of the ambient field, so a nonzero `f_𝔱(θ) ∈ K` can be cancelled.

* `inv_mem_range_of_ringHom_field` — the image of a ring hom from a field into a field is closed under
  inverses of nonzero elements;
* ★★★ `dvd_pred_of_piTilde_pow_mul_mem_ambK` — the dichotomy in the precise form Step 3 needs.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
open Polynomial

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ **The image of a ring hom from a field into a field is closed under inverses of nonzero
elements.** -/
theorem inv_mem_range_of_ringHom_field {K L : Type*} [Field K] [Field L] (f : K →+* L)
    {x : L} (hx : x ∈ Set.range f) (hx0 : x ≠ 0) : x⁻¹ ∈ Set.range f := by
  obtain ⟨y, rfl⟩ := hx
  have hy0 : y ≠ 0 := fun h => hx0 (by rw [h, map_zero])
  exact ⟨y⁻¹, map_inv₀ f y⟩

/-- ★★★ **The `π̃`-dichotomy.**  If `π̃^m · a = S` with `a ∈ K = F_q(θ)`, `a ≠ 0` and
`S ∈ range (ambInfHom F)`, then `(q-1) ∣ m`.  (Contrapositively: if `(q-1) ∤ m` then `a = 0` — the
input Step 3(a) of Dac's §5.3/§6 needs.) -/
theorem dvd_pred_of_piTilde_pow_mul_mem_ambK {m : ℕ} {a S : Ambient F}
    (ha : a ∈ ambK F) (ha0 : a ≠ 0) (hS : S ∈ Set.range (ambInfHom F))
    (h : (ambPiTilde F) ^ m * a = S) :
    (Nat.card F - 1) ∣ m := by
  have haR : a ∈ Set.range (ambInfHom F) := ambK_subset_range_ambInfHom F ha
  have hcancel : (ambPiTilde F) ^ m = S * a⁻¹ := by
    calc (ambPiTilde F) ^ m = (ambPiTilde F) ^ m * (a * a⁻¹) := by
          rw [mul_inv_cancel₀ ha0, mul_one]
      _ = ((ambPiTilde F) ^ m * a) * a⁻¹ := by ring
      _ = S * a⁻¹ := by rw [h]
  refine dvd_pred_of_piTilde_pow_mem_range F ?_
  rw [hcancel]
  exact range_ambInfHom_mul_mem F hS (inv_mem_range_of_ringHom_field (ambInfHom F) haR ha0)

/-- The same dichotomy with a product on the right — the shape in which Step 3(a) presents the
identity (`G := ∏_j Γ_j · b(θ)` and `ambInfHom (ζ_A 𝔰)` are the two factors). -/
theorem dvd_pred_of_piTilde_pow_mul_mem_ambK' {m : ℕ} {a G : Ambient F} {S : Ambient F}
    (ha : a ∈ ambK F) (ha0 : a ≠ 0) (hG : G ∈ ambK F) (hS : S ∈ Set.range (ambInfHom F))
    (h : (ambPiTilde F) ^ m * a = G * S) :
    (Nat.card F - 1) ∣ m :=
  dvd_pred_of_piTilde_pow_mul_mem_ambK F ha ha0
    (range_ambInfHom_mul_mem F (ambK_subset_range_ambInfHom F hG) hS) h

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §4. The dichotomy with a FINITE SUM on the right (the shared-prefix engine) -/

/-- The image of `ambInfHom` is closed under addition. -/
lemma range_ambInfHom_add_mem {x y : Ambient F}
    (hx : x ∈ Set.range (ambInfHom F)) (hy : y ∈ Set.range (ambInfHom F)) :
    x + y ∈ Set.range (ambInfHom F) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, map_add _ _ _⟩

/-- The image of `ambInfHom` is closed under finite sums. -/
lemma range_ambInfHom_finset_sum_mem {ι : Type*} (s : Finset ι) {G : ι → Ambient F}
    (h : ∀ i ∈ s, G i ∈ Set.range (ambInfHom F)) :
    (∑ i ∈ s, G i) ∈ Set.range (ambInfHom F) := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact range_ambInfHom_add_mem F (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- ★★★ **The `π̃`-dichotomy with a finite sum on the right.**  This is the shared-prefix engine: for a
prefix `𝔱` shared by several extenders the bridge produces

  `π̃^m · f_𝔱(θ) = ∑_{s ∈ J(𝔱)} G_s · ambInfHom (ζ_A 𝔰_s)`

with `f_𝔱(θ) ∈ K`, every `G_s ∈ K`, and every `ζ_A 𝔰_s` in the image of the completion; if `f_𝔱(θ) ≠ 0`
then `π̃^m` itself lies in that image, so `(q-1) ∣ m`.  (The remaining case `f_𝔱(θ) = 0` is excluded by
the induction hypothesis on the tails — see `PLAN.md` §«SESSION 355» §3.) -/
theorem dvd_pred_of_piTilde_pow_mul_finset_sum {m : ℕ} {a : Ambient F} {ι : Type*}
    (s : Finset ι) {G S : ι → Ambient F}
    (ha : a ∈ ambK F) (ha0 : a ≠ 0)
    (hG : ∀ i ∈ s, G i ∈ ambK F) (hS : ∀ i ∈ s, S i ∈ Set.range (ambInfHom F))
    (h : (ambPiTilde F) ^ m * a = ∑ i ∈ s, G i * S i) :
    (Nat.card F - 1) ∣ m := by
  have hinv : a⁻¹ ∈ ambK F := (ambK F).inv_mem ha
  have hcancel : (ambPiTilde F) ^ m = a⁻¹ * ∑ i ∈ s, G i * S i := by
    calc (ambPiTilde F) ^ m = (a⁻¹ * a) * (ambPiTilde F) ^ m := by
          rw [inv_mul_cancel₀ ha0, one_mul]
      _ = a⁻¹ * ((ambPiTilde F) ^ m * a) := by ring
      _ = a⁻¹ * ∑ i ∈ s, G i * S i := by rw [h]
  refine dvd_pred_of_piTilde_pow_mem_range F ?_
  rw [hcancel]
  exact range_ambInfHom_mul_mem F (ambK_subset_range_ambInfHom F hinv)
    (range_ambInfHom_finset_sum_mem F s fun i hi =>
      range_ambInfHom_mul_mem F (ambK_subset_range_ambInfHom F (hG i hi)) (hS i hi))

end ZagierHoffmanPositiveChar
