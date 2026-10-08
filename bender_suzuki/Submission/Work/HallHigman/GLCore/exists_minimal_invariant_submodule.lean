import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman.GLCore

/-- **A nonzero invariant submodule of minimal dimension.**  Let `E` act on a nontrivial
finite-dimensional `K`-vector space `V` through `σ`.  Then among the nonzero `σ`-invariant
submodules of `V` there is one of minimal `K`-dimension, and it is `σ`-simple: it contains no
proper nonzero `σ`-invariant submodule. -/
theorem exists_minimal_invariant_submodule {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Nontrivial V] {E : Type*} [Monoid E]
    (σ : E →* Module.End K V) :
    ∃ W : Submodule K V, W ≠ ⊥ ∧ (∀ e : E, ∀ x ∈ W, σ e x ∈ W) ∧
      (∀ U : Submodule K V, U ≤ W → U ≠ ⊥ → (∀ e : E, ∀ x ∈ U, σ e x ∈ U) → U = W) := by
  classical
  -- `⊤` is a nonzero `σ`-invariant submodule, since `V` is nontrivial.
  have htop : (⊤ : Submodule K V) ≠ ⊥ := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have : v ∈ (⊥ : Submodule K V) := h ▸ Submodule.mem_top
    exact hv (by simpa using this)
  have htopinv : ∀ e : E, ∀ x ∈ (⊤ : Submodule K V), σ e x ∈ (⊤ : Submodule K V) :=
    fun _ _ _ => Submodule.mem_top
  -- The set of `K`-dimensions attained by nonzero `σ`-invariant submodules.
  let p : ℕ → Prop := fun n => ∃ W : Submodule K V,
    W ≠ ⊥ ∧ (∀ e : E, ∀ x ∈ W, σ e x ∈ W) ∧ Module.finrank K W = n
  have hpne : ∃ n, p n := ⟨_, ⊤, htop, htopinv, rfl⟩
  -- Pick a nonzero invariant submodule of minimal dimension.
  obtain ⟨W, hWne, hWinv, hWdim⟩ := Nat.find_spec hpne
  refine ⟨W, hWne, hWinv, ?_⟩
  intro U hUle hUne hUinv
  -- `U` is again a nonzero invariant submodule, and `dim U ≤ dim W`.
  have hUp : p (Module.finrank K U) := ⟨U, hUne, hUinv, rfl⟩
  have h1 : Nat.find hpne ≤ Module.finrank K U := Nat.find_min' hpne hUp
  have h2 : Module.finrank K U ≤ Module.finrank K W := Submodule.finrank_mono hUle
  have hdim : Module.finrank K U = Module.finrank K W := le_antisymm h2 (hWdim ▸ h1)
  -- Equal dimension together with `U ≤ W` forces `U = W`.
  exact Submodule.eq_of_le_of_finrank_eq hUle hdim

end Work.HallHigman.GLCore
