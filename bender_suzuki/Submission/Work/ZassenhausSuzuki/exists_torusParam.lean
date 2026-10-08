import Mathlib
import Submission.Work.ZassenhausSuzuki.torusPar_existsUnique
import Submission.Work.ZassenhausSuzuki.torusPar_injective

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The torus parametrisation `D = twoPoint H t → Kˣ` of a torus-coordinatised rank-one group

`TorusCoords K θ H Q t e` records that every `d ∈ D = twoPoint H t` acts on the root group `Q`
by a standard torus element of Higman's group `A(K,θ) = SzA K θ` in the coordinates `e`.  This
file assembles the two structural facts about the induced parametrisation

* existence and uniqueness of the parameter of a single `d` (`torusPar_existsUnique`), and
* faithfulness of the action of `D` on `Q` (`torusPar_injective`),

into the statement that the parameters glue into a single *injective multiplicative* map
`par : G → Kˣ` (defined on all of `G`, arbitrary outside `D`).

Multiplicativity is formal: if `d₁` realises `h_λ` and `d₂` realises `h_μ` on `Q`, then
`d₁ d₂` realises `h_{λμ}`, because conjugation composes and `h_λ ∘ h_μ = h_{λμ}`
(`SzA.hLam_mul`); uniqueness of the parameter then identifies `par (d₁ d₂)` with
`par d₁ * par d₂`.
-/

namespace Work.ZassenhausSuzuki

theorem exists_torusParam {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H)
    {K : Type} [Field K] [CharP K 2] {θ : K ≃+* K} {e : Q ≃* Work.ZassenhausSuzuki.SzA K θ}
    (htorus : Work.ZassenhausSuzuki.TorusCoords K θ H Q t e) :
    ∃ par : G → Kˣ,
      (∀ d ∈ Submission.Blueprint.twoPoint H t, ∀ x : Q,
        (((e.symm (Work.ZassenhausSuzuki.SzA.hLam θ (par d : K) (e x)) : Q)) : G)
          = d * (x : G) * d⁻¹) ∧
      (∀ d₁ ∈ Submission.Blueprint.twoPoint H t, ∀ d₂ ∈ Submission.Blueprint.twoPoint H t,
        par (d₁ * d₂) = par d₁ * par d₂) ∧
      (∀ d₁ ∈ Submission.Blueprint.twoPoint H t, ∀ d₂ ∈ Submission.Blueprint.twoPoint H t,
        par d₁ = par d₂ → d₁ = d₂) := by
  classical
  -- Every `d ∈ D` acts on `Q` through a *unique* torus parameter.
  have hexU : ∀ d : G, d ∈ Submission.Blueprint.twoPoint H t → ∃! lam : Kˣ,
      ∀ x : Q, (((e.symm (SzA.hLam θ (lam : K) (e x)) : Q)) : G)
        = d * (x : G) * d⁻¹ := fun d hd => torusPar_existsUnique htorus hd
  -- Choose that parameter on `D` and the trivial parameter outside `D`.
  let par : G → Kˣ := fun d =>
    if hd : d ∈ Submission.Blueprint.twoPoint H t then Classical.choose (hexU d hd) else 1
  have hpar : ∀ d (hd : d ∈ Submission.Blueprint.twoPoint H t), ∀ x : Q,
      (((e.symm (SzA.hLam θ (par d : K) (e x)) : Q)) : G) = d * (x : G) * d⁻¹ := by
    intro d hd
    have h := (Classical.choose_spec (hexU d hd)).1
    simpa only [par, dite_eq_left hd] using h
  have hpar_eq : ∀ d (hd : d ∈ Submission.Blueprint.twoPoint H t),
      par d = Classical.choose (hexU d hd) := by
    intro d hd
    simp only [par, dite_eq_left hd]
  refine ⟨par, hpar, ?_, ?_⟩
  · -- Multiplicativity: the actions of `d₁` and `d₂` compose.
    intro d₁ h₁ d₂ h₂
    have hd : d₁ * d₂ ∈ Submission.Blueprint.twoPoint H t :=
      (Submission.Blueprint.twoPoint H t).mul_mem h₁ h₂
    have hprod : ∀ x : Q,
        (((e.symm (SzA.hLam θ (((par d₁ * par d₂ : Kˣ)) : K) (e x)) : Q)) : G)
          = (d₁ * d₂) * (x : G) * (d₁ * d₂)⁻¹ := by
      intro x
      -- `d₂` sends `x` to `z`, and `d₁` sends `z` to the conjugate by `d₁ d₂`.
      set z : Q := e.symm (SzA.hLam θ ((par d₂ : Kˣ) : K) (e x)) with hz
      have hzG : (z : G) = d₂ * (x : G) * d₂⁻¹ := hpar d₂ h₂ x
      have h1 : (((e.symm (SzA.hLam θ ((par d₁ : Kˣ) : K) (e z)) : Q)) : G)
          = d₁ * (z : G) * d₁⁻¹ := hpar d₁ h₁ z
      have hez : e z = SzA.hLam θ ((par d₂ : Kˣ) : K) (e x) := by
        rw [hz]; exact MulEquiv.apply_symm_apply e _
      have hkey : e.symm (SzA.hLam θ (((par d₁ * par d₂ : Kˣ)) : K) (e x))
          = e.symm (SzA.hLam θ ((par d₁ : Kˣ) : K) (e z)) := by
        rw [hez, Units.val_mul, SzA.hLam_mul]
      rw [hkey, h1, hzG]
      group
    rw [hpar_eq (d₁ * d₂) hd]
    exact ((Classical.choose_spec (hexU (d₁ * d₂) hd)).2 (par d₁ * par d₂) hprod).symm
  · -- Injectivity: `D` acts faithfully on `Q` (Zassenhaus condition).
    intro d₁ h₁ d₂ h₂ heq
    have hp₂ : ∀ x : Q,
        (((e.symm (SzA.hLam θ ((par d₁ : Kˣ) : K) (e x)) : Q)) : G)
          = d₂ * (x : G) * d₂⁻¹ := by
      intro x
      have h := hpar d₂ h₂ x
      rwa [← heq] at h
    exact torusPar_injective hsplit hzass h₁ h₂ (hpar d₁ h₁) hp₂

end Work.ZassenhausSuzuki
