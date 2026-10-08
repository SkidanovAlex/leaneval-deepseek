import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12

/-- For a homomorphism `φ : V →* A` into a finite cyclic group `A` of order `n`, there
is an element `v₀ : V` whose image generates (as a monoid, hence via natural powers)
the whole image of `φ`, and `φ v₀ ^ n = 1`. -/
theorem existsPowOfCyclic {V A : Type*} [Group V] [Group A] [Finite A] [IsCyclic A] (n : ℕ)
    (hn : Nat.card A = n) (φ : V →* A) :
    ∃ v₀ : V, φ v₀ ^ n = 1 ∧ ∀ v : V, ∃ m : ℕ, φ v = φ v₀ ^ m := by
  classical
  -- The image of `φ` is a subgroup of the cyclic group `A`, hence cyclic and finite.
  -- Pick a generator `x` of `φ.range` in the sense of monoid powers.
  obtain ⟨x, hx⟩ := IsCyclic.exists_monoid_generator (α := φ.range)
  -- Realise `x` as `φ v₀`.
  obtain ⟨v₀, hv₀⟩ := MonoidHom.mem_range.mp x.2
  refine ⟨v₀, ?_, fun v => ?_⟩
  · -- `φ v₀ ^ n = 1` since `n = Nat.card A` and every element of a finite group
    -- has `Nat.card`-th power equal to `1`.
    rw [← hn]
    exact pow_card_eq_one'
  · -- `φ v` lies in `φ.range = zpowers x` (as monoid powers), so it is `x ^ m`.
    have hy : (⟨φ v, MonoidHom.mem_range.mpr ⟨v, rfl⟩⟩ : φ.range) ∈ Submonoid.powers x := hx _
    obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp hy
    refine ⟨m, ?_⟩
    have h1 := congrArg Subtype.val hm
    simp only [Subgroup.coe_pow] at h1
    rw [hv₀]
    exact h1.symm

end Work.ThmF.ChV12
