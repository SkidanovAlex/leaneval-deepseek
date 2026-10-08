import Mathlib
import Submission.Work.BG.CharBridge
import Submission.Work.BG.indexTwoMackey
import Submission.Work.BG.indexTwoInduceIrreducible
import Submission.Work.BG.s02_classSumSquare
import Submission.Work.BG.s02_classSumSquare_vanish
import Submission.OddOrder.GroupTheory.RepresentationTheory.CyclicCharacterExtension
import Submission.OddOrder.GroupTheory.RepresentationTheory.LinearCharacter

/-!
# General index-two character-theory lemmas (auxiliary to `lemma22EvalW`)

Let `N ⊴ K` be a normal subgroup of index two of a finite group `K` and `s ∈ K ∖ N`.

* `Work.BG.exists_linear_extension`: a degree-one irreducible class function `θ` of `N` fixed by
  `s`-conjugation extends to a **homomorphism** `K →* ℂˣ`.
* `Work.BG.induce_apply_coe_of_conjBy_eq`: `(Ind_N^K θ)(n) = 2θ(n)` for `n ∈ N` when
  `θ^s = θ`.
* `Work.BG.sum_induce_eq_two_mul_sq`: for a conjugation-invariant `X ⊆ K ∖ N`,
  `Σ_{x,y ∈ X} (Ind_N^K θ)(xy) = 2 (Σ_{x ∈ X} χ x)^2` when `θ` is `s`-invariant with extension `χ`.
* `Work.BG.sum_induce_eq_zero`: for `X ⊆ K ∖ N` conjugation-invariant and `θ ∈ Irr(N)` with
  `θ^s ≠ θ`, `Σ_{x,y ∈ X} (Ind_N^K θ)(xy) = 0`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

section General

variable {K : Type} [Group K] [Finite K]

/-- **Extension of an `s`-invariant degree-one irreducible character of an index-two normal
subgroup to a homomorphism.**  (Isaacs 11.22 for the cyclic quotient `K/N ≅ C₂`, plus the
"degree one ⟹ multiplicative" packaging of the linear-character library.) -/
theorem exists_linear_extension {N : Subgroup K} [N.Normal] (h2 : N.index = 2) (s : K)
    (hs : s ∉ N) (θ : ClassFunction ↥N ℂ) (hθ : IsIrreducibleCharacter θ) (hθ1 : θ 1 = 1)
    (hinv : ClassFunction.conjBy s θ = θ) :
    ∃ χ : K →* ℂˣ, ∀ n : ↥N, (χ (n : K) : ℂ) = θ n := by
  haveI : Fintype K := Fintype.ofFinite _
  haveI : Fintype ↥N := Fintype.ofFinite _
  have hgen : ∀ k : K, ∃ i : ℤ, (s ^ i)⁻¹ * k ∈ N := by
    intro k
    by_cases hk : k ∈ N
    · exact ⟨0, by simpa using hk⟩
    · refine ⟨1, ?_⟩
      have hs' : s⁻¹ ∉ N := fun h => hs (N.inv_mem_iff.mp h)
      rw [Subgroup.mul_mem_iff_of_index_two h2]
      simp [hs', hk]
  obtain ⟨χ0, hχ0irr, hχ0res⟩ := hθ.exists_extension_of_conjBy_eq hgen hinv
  have hval : ∀ n : ↥N, (χ0 : K → ℂ) (n : K) = θ n := by
    intro n
    have := congrArg (fun f : ClassFunction ↥N ℂ => (f : ↥N → ℂ) n) hχ0res
    simpa [ClassFunction.restrict_apply] using this
  have hχ01 : (χ0 : K → ℂ) 1 = 1 := by
    have := hval (1 : ↥N)
    rw [Subgroup.coe_one] at this
    rw [this]; simpa using hθ1
  obtain ⟨χ, hχ⟩ := hχ0irr.exists_linearIrreducibleCharacter_eq_of_apply_one_eq_one hχ01
  refine ⟨χ, fun n => ?_⟩
  rw [← linearIrreducibleCharacter_apply χ (n : K)]
  have : ((linearIrreducibleCharacter χ).toClassFunction : K → ℂ) (n : K) = χ0 (n : K) :=
    congrArg (fun f : ClassFunction K ℂ => (f : K → ℂ) (n : K)) hχ
  rw [this, hval n]

variable [Fintype K]

/-- **Value of `Ind_N^K θ` on `N`** when `θ^s = θ`: it is `2θ`. -/
theorem induce_apply_coe_of_conjBy_eq {N : Subgroup K} [N.Normal] (h2 : N.index = 2) (s : K)
    (hs : s ∉ N) [Invertible (Nat.card ↥N : ℂ)]
    (θ : ClassFunction ↥N ℂ) (hinv : ClassFunction.conjBy s θ = θ) :
    ∀ n : ↥N, (ClassFunction.induce N θ) (n : K) = 2 * θ n := by
  intro n
  have hmack := indexTwoMackey (H := K) N h2 s hs θ
  have h := congrArg (fun f : ClassFunction ↥N ℂ => (f : ↥N → ℂ) n) hmack
  simp only [ClassFunction.restrict_apply] at h
  rw [h]
  have h2' : (θ + ClassFunction.conjBy s θ) n = 2 * θ n := by
    simp [hinv, two_mul]
  rw [h2']

/-- **The sum identity, invariant case.**  For `X ⊆ K ∖ N` and `θ ∈ Irr(N)` with `θ^s = θ` and
extension `χ : K →* ℂˣ`: `Σ_{x,y ∈ X} (Ind_N^K θ)(xy) = 2 (Σ_{x ∈ X} χ x)^2`. -/
theorem sum_induce_eq_two_mul_sq {N : Subgroup K} [N.Normal] (h2 : N.index = 2) (s : K)
    (hs : s ∉ N) [Invertible (Nat.card ↥N : ℂ)]
    (θ : ClassFunction ↥N ℂ) (hinv : ClassFunction.conjBy s θ = θ)
    (χ : K →* ℂˣ) (hχ : ∀ n : ↥N, (χ (n : K) : ℂ) = θ n)
    (X : Finset K) (hXN : ∀ x ∈ X, x ∉ N) :
    ∑ x ∈ X, ∑ y ∈ X, (ClassFunction.induce N θ) (x * y)
      = 2 * (∑ x ∈ X, (χ x : ℂ)) ^ 2 := by
  have hpoint : ∀ x ∈ X, ∀ y ∈ X, (ClassFunction.induce N θ) (x * y)
      = 2 * ((χ x : ℂ) * (χ y : ℂ)) := by
    intro x hx y hy
    have hxN : x ∉ N := hXN x hx
    have hyN : y ∉ N := hXN y hy
    have hxy : x * y ∈ N := by
      rw [Subgroup.mul_mem_iff_of_index_two h2]; simp [hxN, hyN]
    have h1 := induce_apply_coe_of_conjBy_eq h2 s hs θ hinv ⟨x * y, hxy⟩
    have h2v : θ ⟨x * y, hxy⟩ = (χ x : ℂ) * (χ y : ℂ) := by
      rw [← hχ ⟨x * y, hxy⟩]
      rw [show ((⟨x * y, hxy⟩ : ↥N) : K) = x * y from rfl, map_mul]
      push_cast
      ring
    rw [h1, h2v]
  calc ∑ x ∈ X, ∑ y ∈ X, (ClassFunction.induce N θ) (x * y)
      = ∑ x ∈ X, ∑ y ∈ X, 2 * ((χ x : ℂ) * (χ y : ℂ)) :=
        Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => hpoint x hx y hy
    _ = 2 * (∑ x ∈ X, (χ x : ℂ)) ^ 2 := by
        have hS : (∑ x ∈ X, (χ x : ℂ)) ^ 2
            = ∑ x ∈ X, ∑ y ∈ X, (χ x : ℂ) * (χ y : ℂ) := by
          rw [sq, Finset.sum_mul]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
        rw [hS, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]

/-- **The sum identity, non-invariant case.**  For `X ⊆ K ∖ N` conjugation-invariant and
`θ ∈ Irr(N)` with `θ^s ≠ θ`: `Σ_{x,y ∈ X} (Ind_N^K θ)(xy) = 0`. -/
theorem sum_induce_eq_zero {N : Subgroup K} [N.Normal] (h2 : N.index = 2) (s : K)
    (hs : s ∉ N) [Invertible (Nat.card ↥N : ℂ)] [Invertible (Nat.card K : ℂ)]
    (θ : ClassFunction ↥N ℂ) (hθ : IsIrreducibleCharacter θ) (hinv : ClassFunction.conjBy s θ ≠ θ)
    (X : Finset K) (hX : ∀ g x : K, x ∈ X → g * x * g⁻¹ ∈ X)
    (hXN : ∀ x ∈ X, x ∉ N) :
    ∑ x ∈ X, ∑ y ∈ X, (ClassFunction.induce N θ) (x * y) = 0 := by
  haveI : Fintype ↥N := Fintype.ofFinite _
  have hψirr : IsIrreducibleCharacter (ClassFunction.induce N θ) :=
    indexTwoInduceIrreducible N h2 s hs ⟨θ, hθ⟩ hinv
  have hzero : ∀ x ∈ X, (ClassFunction.induce N θ) x = 0 := by
    intro x hx
    exact ClassFunction.induce_eq_zero_of_not_mem_normal θ (hXN x hx)
  exact s02_classSumSquare_vanish (K := K) X hX (ClassFunction.induce N θ) (Or.inl hψirr) hzero

end General

end Work.BG
