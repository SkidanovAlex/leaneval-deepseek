import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausPSL2.ZData.dStab_fpf_on_Q

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Injectivity of the torus parametrisation on `D = H ∩ Hᵗ`

Let `G` be a finite group with a split rank-one Zassenhaus configuration `(H, Q, t)` and let
`e : Q ≃* A(K,θ)` be a coordinatisation of the root group by Higman's group `A(K,θ)`.  The
two-point stabiliser `D = twoPoint H t = H ∩ Hᵗ` acts on `Q` by conjugation, while the standard
torus `Λ = h(Kˣ)` acts on `A(K,θ)` through `h_λ`.

This lemma is the *injectivity* half of the statement that `D → Λ`, `d ↦ h_{λ(d)}`, is a
bijection: if `d₁, d₂ ∈ D` induce the same automorphism of `Q` (`p₁`, `p₂` — both send the
conjugate of `x` to `h_λ` in the coordinates `e`), then `d₁ = d₂`.

The mathematical content is exactly the faithfulness of the conjugation action of `D` on `Q`:
the quotient `d₂⁻¹ d₁` centralises `Q`, and by `dStab_fpf_on_Q` a non-identity element of `D`
has no non-trivial fixed point on `Q`; since `Q ≠ ⊥` (a consequence of the coordinatisation
`Q ≃* A(K,θ)` with `K` a field), this forces the quotient to be `1`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ZassenhausSuzuki

/-- The root group `Q` is non-trivial: it is coordinatised by `A(K,θ) = K × K` with `K` a field,
which contains the element `⟨1,0⟩ ≠ 1`. -/
theorem Q_ne_bot_of_mulEquivSzA {G : Type*} [Group G] {Q : Subgroup G}
    {K : Type} [Field K] {θ : K ≃+* K} {e : Q ≃* SzA K θ} : Q ≠ ⊥ := by
  intro hbot
  have hmem : ((e.symm (⟨1, 0⟩ : SzA K θ) : Q) : G) ∈ (⊥ : Subgroup G) := by
    rw [← hbot]
    simpa using (e.symm (⟨1, 0⟩ : SzA K θ)).2
  have h1 : (e.symm (⟨1, 0⟩ : SzA K θ) : Q) = 1 := by
    apply Subtype.ext
    simpa using Subgroup.mem_bot.mp hmem
  have h1' : (⟨1, 0⟩ : SzA K θ) = 1 := by
    have := congrArg (fun q : Q => e q) h1
    simpa using this
  have h10 : (1 : K) = 0 := by
    have := congrArg (fun z : SzA K θ => z.a) h1'
    simpa using this
  exact one_ne_zero h10

theorem torusPar_injective {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H)
    {K : Type} [Field K] [CharP K 2] {θ : K ≃+* K} {e : Q ≃* Work.ZassenhausSuzuki.SzA K θ}
    {lam : Kˣ} {d₁ d₂ : G}
    (h₁ : d₁ ∈ Submission.Blueprint.twoPoint H t)
    (h₂ : d₂ ∈ Submission.Blueprint.twoPoint H t)
    (p₁ : ∀ x : Q, (((e.symm (Work.ZassenhausSuzuki.SzA.hLam θ (lam : K) (e x)) : Q)) : G)
        = d₁ * (x : G) * d₁⁻¹)
    (p₂ : ∀ x : Q, (((e.symm (Work.ZassenhausSuzuki.SzA.hLam θ (lam : K) (e x)) : Q)) : G)
        = d₂ * (x : G) * d₂⁻¹) :
    d₁ = d₂ := by
  classical
  -- `Q` has a non-identity element, since it is coordinatised by the non-trivial group `A(K,θ)`.
  have hQ : Q ≠ ⊥ := Q_ne_bot_of_mulEquivSzA (K := K) (θ := θ) (e := e)
  obtain ⟨x₀, hx₀Q, hx₀ne⟩ : ∃ x : G, x ∈ Q ∧ x ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact hQ (Subgroup.eq_bot_iff_forall Q |>.mpr (fun x hx => hcon x hx))
  -- `d₂⁻¹ * d₁ ∈ D` and it centralises `Q`.
  have hg : d₂⁻¹ * d₁ ∈ Submission.Blueprint.twoPoint H t :=
    (Submission.Blueprint.twoPoint H t).mul_mem
      ((Submission.Blueprint.twoPoint H t).inv_mem h₂) h₁
  have hconj : ∀ x : G, x ∈ Q →
      (d₂⁻¹ * d₁) * x * (d₂⁻¹ * d₁)⁻¹ = x := by
    intro x hx
    have h1 := p₁ ⟨x, hx⟩
    have h2 := p₂ ⟨x, hx⟩
    have heq : d₁ * x * d₁⁻¹ = d₂ * x * d₂⁻¹ := h1.symm.trans h2
    calc (d₂⁻¹ * d₁) * x * (d₂⁻¹ * d₁)⁻¹
        = d₂⁻¹ * (d₁ * x * d₁⁻¹) * d₂ := by group
      _ = d₂⁻¹ * (d₂ * x * d₂⁻¹) * d₂ := by rw [heq]
      _ = x := by group
  by_cases hg1 : d₂⁻¹ * d₁ = 1
  · calc d₁ = d₂ * (d₂⁻¹ * d₁) := by group
      _ = d₂ * 1 := by rw [hg1]
      _ = d₂ := by group
  · exfalso
    exact hx₀ne (Work.ZassenhausPSL2.ZData.dStab_fpf_on_Q H Q t hsplit hzass
      (d₂⁻¹ * d₁) hg hg1 x₀ hx₀Q (hconj x₀ hx₀Q))

end Work.ZassenhausSuzuki
