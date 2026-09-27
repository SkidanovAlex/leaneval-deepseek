import Mathlib
import Submission.Work.Mostow.bieberbachDefs

/-!
# The Engel sequence inside a finite subgroup of `O(m)`

Definitions used by `Work.Mostow.orthSmallCommute`.

For a subgroup `A ≤ O(m)` of the orthogonal group of `E m = EuclideanSpace ℝ (Fin m)` and
elements `a b : A`, the **Engel sequence** is

`B₀ = b`,  `B_{i+1} = a * B_i * a⁻¹ * B_i⁻¹ = [a, B_i]`.

Buser's commutator estimate (`Work.Mostow.mOf_commutator`) then gives
`mOf B_{i+1} ≤ 2 * mOf a * mOf B_i`, so if `mOf a ≤ 1/4` and `mOf b ≤ 1/4` the sequence shrinks
geometrically; finiteness of `A` forces one term to be `1`; and the Engel–Frobenius lemma
(`Work.Mostow.Margulis.engel_frobenius_orthogonal`) descends from `B_{i+2} = 1` to `B_{i+1} = 1`.
-/

namespace Work.Mostow

open Submission.Mostow

noncomputable section

variable {m : ℕ}

/-- The Engel step `x ↦ a x a⁻¹ x⁻¹`, as a self-map of a subgroup `A ≤ O(m)`. -/
def engelStep (A : Subgroup (E m ≃ₗᵢ[ℝ] E m)) (a : A) : A → A :=
  fun x => ⟨(a : E m ≃ₗᵢ[ℝ] E m) * (x : E m ≃ₗᵢ[ℝ] E m)
      * (a : E m ≃ₗᵢ[ℝ] E m)⁻¹ * (x : E m ≃ₗᵢ[ℝ] E m)⁻¹,
    A.mul_mem (A.mul_mem (A.mul_mem a.2 x.2) (A.inv_mem a.2)) (A.inv_mem x.2)⟩

/-- The Engel sequence `B₀ = b`, `B_{i+1} = [a, B_i]` inside a subgroup `A ≤ O(m)`. -/
def engelSeq (A : Subgroup (E m ≃ₗᵢ[ℝ] E m)) (a b : A) : ℕ → A :=
  fun i => Nat.rec b (fun _ x => engelStep A a x) i

@[simp] lemma engelSeq_zero (A : Subgroup (E m ≃ₗᵢ[ℝ] E m)) (a b : A) :
    engelSeq A a b 0 = b := rfl

lemma engelSeq_succ (A : Subgroup (E m ≃ₗᵢ[ℝ] E m)) (a b : A) (i : ℕ) :
    ((engelSeq A a b (i + 1) : A) : E m ≃ₗᵢ[ℝ] E m)
      = (a : E m ≃ₗᵢ[ℝ] E m) * (engelSeq A a b i : E m ≃ₗᵢ[ℝ] E m)
          * (a : E m ≃ₗᵢ[ℝ] E m)⁻¹ * (engelSeq A a b i : E m ≃ₗᵢ[ℝ] E m)⁻¹ := rfl

end

end Work.Mostow
