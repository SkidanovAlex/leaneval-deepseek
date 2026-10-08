/-
Bender–Glauberman 1981, Lemma 1.8 in the mod-2 form needed by Lemma 1.9
(`Work.GW2.C23.ModTwoIndepProp`, stated in `BG/Thm43Defs.lean`).

Lemma 1.8 (paper, exact form): if `∑ᵢ cᵢ βᵢ = 0` with algebraic integers `cᵢ` and pairwise
distinct irreducible characters `βᵢ` of a `2'`-group `B`, then every `cᵢ = 0`; the paper's
one-line proof is `cᵢ = (β, βᵢ)_B = 0`.

Lemma 1.9 (uniqueness of the Glauberman correspondent) actually needs the *congruence*
form: `∑ᵢ cᵢ βᵢ ≡ 0 (mod 2)` pointwise forces `cᵢ ≡ 0 (mod 2)`.  The proof is the same
orthogonality computation, kept at the level of algebraic integers:

* `β := ∑ᵢ cᵢ • βᵢ` is a class function and `(β, βₖ)_B = cₖ` by first orthogonality
  (`irreducibleCharacter_inner_eq_ite`) together with injectivity of `i ↦ βᵢ`;
* multiplying by `|B|`: `|B| · cₖ = ∑_{b ∈ B} β(b) · star(βₖ(b))`, and each `β(b) = 2 d(b)`
  with `d(b)` an algebraic integer, so the right-hand side is `2 ·` (an algebraic integer);
* hence `|B| cₖ ≡ 0 (mod 2)`; since `|B|` is odd, `|B| cₖ ≡ cₖ (mod 2)`, and therefore
  `cₖ ≡ 0 (mod 2)`.

The only group-theoretic input is `|B|` odd (used both to make `star(βₖ(b))` integral —
characters of finite groups take algebraic-integer values — and to invert `|B|` mod 2).
-/
import Mathlib
import Submission.Work.BG.Thm43Defs
import Submission.Work.BG.S02
import Submission.Work.BG.CharBridge
import Submission.Work.BG.lemma18LinearIndependent

namespace Work.BG

open OddOrder.RepresentationTheory

/-! ## 0. Integrality of character values (and of their stars) -/

/-- The value of an irreducible character at any group element is an algebraic integer
(it is the trace of a finite-order operator). -/
theorem isIntegral_apply_of_isIrreducibleCharacter {K : Type*} [Group K] [Finite K]
    {φ : ClassFunction K ℂ} (h : IsIrreducibleCharacter φ) (g : K) :
    IsIntegral ℤ (φ g) := by
  obtain ⟨V, _, _, _, ρ, _, hchar⟩ := h
  rw [congrFun hchar g]
  exact character_isIntegral ρ g

/-- The complex conjugate of an irreducible character value is an algebraic integer:
`star (φ g) = φ g⁻¹` (`character_inv`) is again a character value. -/
theorem isIntegral_star_apply_of_isIrreducibleCharacter {K : Type*} [Group K] [Finite K]
    {φ : ClassFunction K ℂ} (h : IsIrreducibleCharacter φ) (g : K) :
    IsIntegral ℤ (star (φ g)) := by
  have h1 : star (φ g) = φ g⁻¹ := by
    obtain ⟨V, _, _, _, ρ, _, hchar⟩ := h
    rw [congrFun hchar g, congrFun hchar g⁻¹, character_inv ρ g]
  rw [h1]
  exact isIntegral_apply_of_isIrreducibleCharacter h g⁻¹

/-! ## 1. Linearity of the class-function inner product in the first argument -/

/-- `ClassFunction.inner` is additive and `ℂ`-linear in its first argument; this is the
finite-sum form used below. -/
theorem inner_sum_smul_left {K : Type*} [Group K] [Fintype K]
    [Invertible (Nat.card K : ℂ)]
    {ι : Type*} (s : Finset ι) (d : ι → ℂ) (β : ι → ClassFunction K ℂ)
    (ψ : ClassFunction K ℂ) :
    ClassFunction.inner (∑ i ∈ s, d i • β i) ψ =
      ∑ i ∈ s, d i * ClassFunction.inner (β i) ψ := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.inner_add_left,
      ClassFunction.inner_smul_left, ih]

/-- The `Finset.univ` form of `inner_sum_smul_left`. -/
theorem inner_sum_smul_left_univ {K : Type*} [Group K] [Fintype K]
    [Invertible (Nat.card K : ℂ)]
    {ι : Type*} [Fintype ι] (d : ι → ℂ) (β : ι → ClassFunction K ℂ)
    (ψ : ClassFunction K ℂ) :
    ClassFunction.inner (∑ i, d i • β i) ψ =
      ∑ i, d i * ClassFunction.inner (β i) ψ := by
  simpa using inner_sum_smul_left (Finset.univ : Finset ι) d β ψ

/-! ## 2. Lemma 1.8, mod-2 form -/

/-- **Lemma 1.8 (Bender–Glauberman), mod-2 form.**

Let `K` be a finite group of odd order, `β : ι → ClassFunction K ℂ` a family of pairwise
distinct irreducible characters (injectivity of `β`) and `c : ι → ℂ` a family of algebraic
integers with `∑ᵢ cᵢ βᵢ(g) ≡ 0 (mod 2)` for every `g`.  Then `cᵢ ≡ 0 (mod 2)` for every `i`.

Unfolded form of `Work.GW2.C23.ModTwoIndepProp`. -/
theorem modTwoIndepAux :
    ∀ {K : Type} [Group K] [Fintype K] [Invertible (Nat.card K : ℂ)], Odd (Nat.card K) →
    ∀ {ι : Type} [Fintype ι] (β : ι → ClassFunction K ℂ),
      (∀ i, IsIrreducibleCharacter (β i)) → Function.Injective β → ∀ c : ι → ℂ,
        (∀ i, IsIntegral ℤ (c i)) → (∀ g : K, AlgIntModTwo (∑ i, c i * β i g) 0) →
          ∀ i, AlgIntModTwo (c i) 0 := by
  intro K _ _ _ hodd ι _ β hβ hinj c hc hmod k
  -- the class function `β := ∑ᵢ cᵢ βᵢ` and its witnesses of `≡ 0 (mod 2)`
  have hmod' : ∀ g : K, ∃ d' : ℂ, IsIntegral ℤ d' ∧ (∑ i, c i * β i g) = 2 * d' := by
    intro g
    obtain ⟨d', hd', heq⟩ := hmod g
    exact ⟨d', hd', by simpa using heq⟩
  choose d hdint hdeq using hmod'
  let βsum : ClassFunction K ℂ := ∑ i, c i • β i
  have hβsum_apply : ∀ g : K, βsum g = ∑ i, c i * β i g := by
    intro g
    simp [βsum]
  -- first orthogonality: `(β, βₖ) = cₖ`
  have hinner : ClassFunction.inner βsum (β k) = c k := by
    have h : ClassFunction.inner βsum (β k) =
        ∑ i, c i * ClassFunction.inner (β i) (β k) :=
      inner_sum_smul_left_univ c β (β k)
    rw [h]
    rw [Finset.sum_eq_single k]
    · have h1 : ClassFunction.inner (β k) (β k) = 1 := by
        have := irreducibleCharacter_inner_eq_ite
          (⟨β k, hβ k⟩ : IrreducibleCharacter K) ⟨β k, hβ k⟩
        simpa using this
      rw [h1, mul_one]
    · intro i _ hik
      have hne : (⟨β i, hβ i⟩ : IrreducibleCharacter K) ≠ ⟨β k, hβ k⟩ := by
        intro hh
        exact hik (hinj (Subtype.ext_iff.mp hh))
      have h1 : ClassFunction.inner (β i) (β k) = 0 := by
        have := irreducibleCharacter_inner_eq_ite
          (⟨β i, hβ i⟩ : IrreducibleCharacter K) ⟨β k, hβ k⟩
        rw [ite_eq_right hne] at this
        simpa using this
      rw [h1, mul_zero]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  -- multiply by `|K|` and expand the unscaled inner sum
  have hcard : (Nat.card K : ℂ) * c k = ClassFunction.innerSum βsum (β k) := by
    rw [← ClassFunction.card_mul_inner βsum (β k), hinner]
  have hsum_int : IsIntegral ℤ (∑ g : K, d g * star ((β k) g)) := by
    refine IsIntegral.sum _ fun g _ => ?_
    exact (hdint g).mul (isIntegral_star_apply_of_isIrreducibleCharacter (hβ k) g)
  have hinnerSum_eq : ClassFunction.innerSum βsum (β k) =
      2 * (∑ g : K, d g * star ((β k) g)) := by
    rw [ClassFunction.innerSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    rw [hβsum_apply g, hdeq g]
    ring
  -- `|K| cₖ ≡ 0 (mod 2)`
  have h2 : AlgIntModTwo ((Nat.card K : ℂ) * c k) 0 := by
    have he : (Nat.card K : ℂ) * c k = 2 * (∑ g : K, d g * star ((β k) g)) := by
      rw [hcard, hinnerSum_eq]
    rw [he]
    exact AlgIntModTwo.mul_two hsum_int
  -- `|K| cₖ ≡ cₖ (mod 2)` because `|K|` is odd
  obtain ⟨n, hn⟩ := hodd
  have h1 : AlgIntModTwo ((Nat.card K : ℂ) * c k) (c k) := by
    refine ⟨(n : ℂ) * c k, (isIntegral_natCast n).mul (hc k), ?_⟩
    rw [hn]
    push_cast
    ring
  exact h1.symm.trans h2

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23 in
theorem modTwoIndep : Work.GW2.C23.ModTwoIndepProp := by
  unfold Work.GW2.C23.ModTwoIndepProp
  exact modTwoIndepAux

end Work.BG
