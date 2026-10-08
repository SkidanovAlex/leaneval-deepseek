import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.RankOneUniqueness.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `ZassenhausSuzuki`: the interface lemmas

The uniqueness of the book's map `f` on the root group (Peterfalvi II Ch. VII §1, p. 268:
`txt = g(x)h(x)tf(x)` with `f` *uniquely* determined), and the Suzuki configuration, the
datum that the family-specific computation produces and that the shared recognition
interface consumes.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness

namespace Work.ZassenhausSuzuki

variable {G : Type*} [Group G] {H Q : Subgroup G} {t : G}

/-- **Uniqueness of `f`.**  If `FRel H t x y₁` and `FRel H t x y₂` with `y₁, y₂ ∈ Q`, then
`y₁ = y₂`.  (This is Peterfalvi II Ch. VII §1's uniqueness of the canonical form
`G ∖ H = H·t·Q`: from `m₁ t y₁ = m₂ t y₂` one gets `y₂y₁⁻¹ ∈ Q ∩ H^t ⊆ Q ⊓ twoPoint H t = 1`.)

Note that `x` is not used beyond being the common left factor `t x t`. -/
theorem frel_unique (hsplit : IsSplitRankOne H Q t) {x y₁ y₂ : G}
    (h₁ : FRel H t x y₁) (h₂ : FRel H t x y₂) (hy₁ : y₁ ∈ Q) (hy₂ : y₂ ∈ Q) :
    y₁ = y₂ := by
  obtain ⟨m₁, hm₁H, hm₁⟩ := h₁
  obtain ⟨m₂, hm₂H, hm₂⟩ := h₂
  -- `t * t = 1` and `t⁻¹ = t`
  have ht2 : t * t = 1 := by
    have h : t ^ orderOf t = 1 := pow_orderOf_eq_one t
    rw [hsplit.invol, pow_two] at h
    exact h
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hmul : m₁ * t * y₁ = m₂ * t * y₂ := hm₁.symm.trans hm₂
  -- (t m₂ t)⁻¹ (t m₁ t) = y₂ y₁⁻¹
  have key : (t * m₂ * t)⁻¹ * (t * m₁ * t) = y₂ * y₁⁻¹ := by
    have h2 : t * m₁ * t = (t * m₂ * t) * (y₂ * y₁⁻¹) := by
      calc t * m₁ * t = t * (m₁ * t * y₁) * y₁⁻¹ := by group
        _ = t * (m₂ * t * y₂) * y₁⁻¹ := by rw [hmul]
        _ = (t * m₂ * t) * (y₂ * y₁⁻¹) := by group
    rw [h2]; group
  -- membership in `Q ⊓ twoPoint H t`
  have hQ : y₂ * y₁⁻¹ ∈ Q := Subgroup.mul_mem Q hy₂ (Subgroup.inv_mem Q hy₁)
  have hconj : y₂ * y₁⁻¹ ∈ conj t H := by
    rw [← key]
    refine Subgroup.mul_mem _ (Subgroup.inv_mem _ ?_) ?_
    · rw [conj, Subgroup.mem_map]
      exact ⟨m₂, hm₂H, by simp [MulAut.conj_apply, htinv]⟩
    · rw [conj, Subgroup.mem_map]
      exact ⟨m₁, hm₁H, by simp [MulAut.conj_apply, htinv]⟩
  have hbot : y₂ * y₁⁻¹ ∈ (⊥ : Subgroup G) := by
    have hmem : y₂ * y₁⁻¹ ∈ Q ⊓ twoPoint H t := ⟨hQ, hsplit.le hQ, hconj⟩
    rwa [hsplit.inf_eq] at hmem
  have h1 : y₂ * y₁⁻¹ = 1 := Subgroup.mem_bot.mp hbot
  exact (mul_inv_eq_one.mp h1).symm

/-- **The Suzuki configuration** on a group `G`: a split rank-one configuration `H = Q ⋊ D`,
`t` (`Submission.Blueprint.IsSplitRankOne`; the faithfulness `IsZassenhaus H` is recorded
separately), together with a field `K` carrying a Tits endomorphism `θ` and an explicit
coordinatisation `e : Q ≃* A(K,θ)` of the root group by Higman's group, under which the
book's map `f` — characterised on `Q^#` by `t x t = m · t · f(x)` (`FRel H t x y`) — is the
Suzuki map `τ = sigma`.

This is the "family-specific part" of the recognition of `Sz(2^n)`: the coordinatisation of
`Q` by `A(K,θ)` (Higman's theorem, `HigmanProp`) and the computation of `f = τ` (Suzuki 1962,
§4–5; Baumeister–Grüninger §5.16–5.21).  The shared recognition interface
`Work.RankOneUniqueness.recognize` (S6 of the lead's design) consumes precisely `e` together
with the `f`-formula `he` below. -/
structure IsSuzukiConfiguration (G : Type*) [Group G] (H Q : Subgroup G) (t : G)
    (K : Type*) [Field K] (θ : K ≃+* K) : Type _ where
  /-- the underlying split rank-one configuration -/
  split : IsSplitRankOne H Q t
  /-- the pointwise stabiliser of three points is trivial -/
  zassenhaus : IsZassenhaus H
  /-- `Q` is non-abelian (the Suzuki case) -/
  nonabelian : ¬ IsAbelianSubgroup Q
  /-- the coordinatisation of the root group by Higman's group `A(K,θ)` -/
  e : Q ≃* SzA K θ
  /-- the book's map `f` is the Suzuki map `τ` in these coordinates -/
  frel : ∀ x : Q, x ≠ 1 →
    FRel H t (x : G) (((e.symm (SzA.sigma θ (e x)) : Q) : G))

namespace IsSuzukiConfiguration

variable {G : Type*} [Group G] {H Q : Subgroup G} {t : G}
variable {K : Type*} [Field K] {θ : K ≃+* K}

/-- The `f`-formula of a Suzuki configuration, in the form consumed by the recognition
lemma: if `FRel H t x y` with `x, y ∈ Q` and `x ≠ 1`, then `e y = τ (e x)`. -/
theorem frel_eq (c : IsSuzukiConfiguration G H Q t K θ) {x y : Q} (hx : (x : G) ≠ 1)
    (h : FRel H t (x : G) (y : G)) : c.e y = SzA.sigma θ (c.e x) := by
  have h1 : y = c.e.symm (SzA.sigma θ (c.e x)) := by
    apply Subtype.ext
    exact frel_unique c.split h (c.frel x (by simpa using hx)) y.2
      (c.e.symm (SzA.sigma θ (c.e x))).2
  rw [h1, MulEquiv.apply_symm_apply]

end IsSuzukiConfiguration

end Work.ZassenhausSuzuki
