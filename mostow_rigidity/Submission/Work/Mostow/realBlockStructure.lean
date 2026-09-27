import Mathlib
import Submission.Work.Mostow.abelianBlockDefs
import Submission.Work.Mostow.isometryEqOfSymPartEq
import Submission.Work.Mostow.action_eq_smul_half_of_oSym_eq_smul

namespace Work.Mostow

/-- **Structure of a "real" block of a family of orthogonal maps.**

Let `ρ : G →* O(V)` (`V` a finite-dimensional real inner product space) and let `W ≠ ⊥` be a
`ρ`-invariant subspace on which every `ρ g` has scalar symmetric part, but where *no* `g` has a
scalar with square `< 4`:
`∀ g, ∃ a, ∀ x ∈ W, oSym (ρ g) x = a • x` and
`∀ g, ¬ ∃ a, (∀ x ∈ W, oSym (ρ g) x = a • x) ∧ a ^ 2 < 4`.

Then there is a sign character `τ : G →* Multiplicative (ZMod 2)` such that every `ρ g` acts on `W`
by the scalar `±1` given by `τ`, and `‖(ρ g) x - x‖ = (if τ g = 1 then 0 else 2) ‖x‖`.

Route.  For `g ∈ G` let `a` be its scalar (`hscal`).  As in `Work.Mostow.complexBlockStructure`,
`|a| ≤ 2` (Cauchy–Schwarz using that the adjoint of `ρ g` is `(ρ g)⁻¹` and `W ≠ ⊥`), and the second
hypothesis says `¬ (a^2 < 4)`, so `a^2 = 4` and `a/2 = ±1`.  Apply
`Submission.Work.Mostow.isometryEqOfSymPartEq` (with `c = a/2`, which is `1` or `-1`) to conclude
`(ρ g) x = (a/2) • x` for `x ∈ W`.  The scalar `a` is unique (`W ≠ ⊥`), so the sign `a/2 = ±1` is
well defined; put `τ g := 1` if `a/2 = 1` and `τ g := 0` otherwise (identifying
`Multiplicative (ZMod 2)` with `{±1}`).  Multiplicativity of `τ` is immediate from
`ρ (g * g') = ρ g * ρ g'` (the scalars multiply, and signs multiply in `{±1}`); `τ 1 = 1`.  The
norm identity follows from `(ρ g) x = ± x`.  Note `G` need not be abelian. -/
theorem realBlockStructure {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {G : Type*} [Group G] (ρ : G →* (V ≃ₗᵢ[ℝ] V))
    (W : Submodule ℝ V) (hWne : W ≠ ⊥)
    (hW : ∀ g : G, ∀ x ∈ W, ρ g x ∈ W)
    (hscal : ∀ g : G, ∃ a : ℝ, ∀ x ∈ W, oSym (ρ g) x = a • x)
    (hreal : ∀ g : G, ¬ ∃ a : ℝ, (∀ x ∈ W, oSym (ρ g) x = a • x) ∧ a ^ 2 < 4) :
    ∃ τ : G →* Multiplicative (ZMod 2), ∀ g : G, ∀ x ∈ W,
      (ρ g) x = (if τ g = 1 then x else -x) ∧
      ‖(ρ g) x - x‖ = (if τ g = 1 then (0:ℝ) else 2) * ‖x‖ := by
  classical
  -- For each `g` choose its scalar `a g`, and put `c g := a g / 2`.
  let a : G → ℝ := fun g => (hscal g).choose
  have ha : ∀ g : G, ∀ x ∈ W, oSym (ρ g) x = a g • x := fun g => (hscal g).choose_spec
  let c : G → ℝ := fun g => a g / 2
  -- `hreal` upgrades `a g` to a scalar with square `4`, so `ρ g` acts on `W` by `c g = ±1`.
  have hmain : ∀ g : G, (∀ x ∈ W, (ρ g) x = c g • x) ∧ (c g = 1 ∨ c g = -1) := by
    intro g
    have h4 : ¬ (a g) ^ 2 < 4 := fun hlt => hreal g ⟨a g, ha g, hlt⟩
    exact action_eq_smul_half_of_oSym_eq_smul (ρ g) W hWne (hW g) (a g) (ha g) h4
  -- On `W ≠ ⊥` a scalar is unique.
  have huneq : ∀ (A : V →ₗ[ℝ] V) (u v : ℝ),
      (∀ x ∈ W, A x = u • x) → (∀ x ∈ W, A x = v • x) → u = v := by
    intro A u v hu hv
    obtain ⟨x, hxW, hx0⟩ := (Submodule.ne_bot_iff W).mp hWne
    have h1 : u • x = v • x := (hu x hxW).symm.trans (hv x hxW)
    have h2 : (u - v) • x = 0 := by rw [sub_smul, h1, sub_self]
    have h3 : u - v = 0 := by
      rcases smul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd h hx0
    linarith
  -- The scalars multiply under `ρ (g * g') = ρ g * ρ g'`.
  have hcmul : ∀ g g' : G, c (g * g') = c g * c g' := by
    intro g g'
    refine huneq ((ρ (g * g') : V ≃ₗᵢ[ℝ] V) : V →ₗ[ℝ] V) _ _ ?_ ?_
    · intro x hx
      exact (hmain (g * g')).1 x hx
    · intro x hx
      have hx' : (ρ g') x ∈ W := hW g' x hx
      calc (ρ (g * g')) x = (ρ g) ((ρ g') x) := by rw [map_mul]; rfl
        _ = c g • ((ρ g') x) := (hmain g).1 _ hx'
        _ = c g • (c g' • x) := by rw [(hmain g').1 x hx]
        _ = (c g * c g') • x := by rw [smul_smul]
  -- A multiplicative `{±1}`-valued scalar on a group is a monoid homomorphism into
  -- `Multiplicative (ZMod 2)`, where the non-identity element is `ofAdd 1`.
  have hchar : ∃ τ : G →* Multiplicative (ZMod 2), ∀ g : G, (τ g = 1 ↔ c g = 1) := by
    let s : G → ZMod 2 := fun g => if c g = 1 then 0 else 1
    have key : ∀ g, c g = -1 → s g = 1 := by
      intro g hg
      show (if c g = 1 then (0:ZMod 2) else 1) = 1
      rw [ite_eq_right]
      · rw [hg]; norm_num
    have key' : ∀ g, c g = 1 → s g = 0 := by
      intro g hg
      show (if c g = 1 then (0:ZMod 2) else 1) = 0
      rw [ite_eq_left hg]
    have hs_mul : ∀ g g', s (g * g') = s g + s g' := by
      intro g g'
      have h := hcmul g g'
      rcases (hmain g).2 with hg | hg <;> rcases (hmain g').2 with hg' | hg'
      · have h1 : c (g * g') = 1 := by rw [h, hg, hg', mul_one]
        rw [key' _ h1, key' _ hg, key' _ hg', add_zero]
      · have h1 : c (g * g') = -1 := by rw [h, hg, hg', mul_neg, one_mul]
        rw [key _ h1, key' _ hg, key _ hg', zero_add]
      · have h1 : c (g * g') = -1 := by rw [h, hg, hg', neg_mul, one_mul]
        rw [key _ h1, key _ hg, key' _ hg', add_zero]
      · have h1 : c (g * g') = 1 := by rw [h, hg, hg', neg_mul_neg, one_mul]
        rw [key' _ h1, key _ hg, key _ hg']
        decide
    have hof : ∀ x : ZMod 2, (Multiplicative.ofAdd x = 1 ↔ x = 0) := by
      intro x
      constructor
      · intro h
        have := congrArg Multiplicative.toAdd h
        simpa using this
      · intro h; rw [h]; rfl
    have hsc : ∀ g, c g = 1 ↔ s g = 0 := by
      intro g
      rcases (hmain g).2 with hg | hg
      · rw [key' _ hg]; exact ⟨fun _ => rfl, fun _ => hg⟩
      · rw [key _ hg]
        exact ⟨fun h => absurd (h.symm.trans hg) (by norm_num), fun h => absurd h (by decide)⟩
    let τ : G →* Multiplicative (ZMod 2) :=
      MonoidHom.mk' (fun g => Multiplicative.ofAdd (s g)) (fun g g' => by rw [hs_mul]; rfl)
    exact ⟨τ, fun g => by
      show Multiplicative.ofAdd (s g) = 1 ↔ c g = 1
      rw [hof (s g)]; exact (hsc g).symm⟩
  obtain ⟨τ, hτ⟩ := hchar
  refine ⟨τ, ?_⟩
  intro g x hx
  have hcg : (ρ g) x = c g • x := (hmain g).1 x hx
  have hc1 : c g = 1 ∨ c g = -1 := (hmain g).2
  have hne : c g = -1 ↔ τ g ≠ 1 := by
    constructor
    · intro h hh
      have : c g = 1 := (hτ g).mp hh
      rw [h] at this; norm_num at this
    · intro hh
      rcases hc1 with h1 | h1
      · exact absurd ((hτ g).mpr h1) hh
      · exact h1
  constructor
  · by_cases h : τ g = 1
    · rw [ite_eq_left h, hcg, (hτ g).mp h, one_smul]
    · rw [ite_eq_right h, hcg, hne.mpr h, neg_one_smul]
  · by_cases h : τ g = 1
    · rw [ite_eq_left h, hcg, (hτ g).mp h, one_smul, sub_self, norm_zero, zero_mul]
    · rw [ite_eq_right h, hcg, hne.mpr h, neg_one_smul]
      rw [show (-x - x : V) = (-2 : ℝ) • x by module]
      rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]

end Work.Mostow
