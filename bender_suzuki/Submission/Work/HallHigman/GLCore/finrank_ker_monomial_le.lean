import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman.GLCore

/-- **Fixed points of a monomial operator.** Let `Q` be a finite type, `g` a permutation of `Q`,
`B` a finite-dimensional `K`-vector space and `T` the "monomial" operator on `Q → B` given by
`(T β) q = c q • Φ (β (g q))`. If `R` meets every `g`-orbit (every element of `Q` is a `g`-iterate
of an element of `R`), then the fixed space of `T` has dimension at most `#R * dim B`. -/
lemma finrank_ker_monomial_le {Q : Type*} [Fintype Q] {K : Type*} [Field K]
    {B : Type*} [AddCommGroup B] [Module K B] [FiniteDimensional K B]
    (g : Equiv.Perm Q) (c : Q → K) (Φ : B →ₗ[K] B) (T : (Q → B) →ₗ[K] (Q → B))
    (hT : ∀ β q, T β q = c q • Φ (β (g q)))
    (R : Finset Q) (hR : ∀ q, ∃ k : ℕ, (g ^ k) q ∈ R) :
    Module.finrank K (LinearMap.ker (T - 1)) ≤ R.card * Module.finrank K B := by
  -- Restriction of a vector to the orbit representatives `R`.
  let restr : (Q → B) →ₗ[K] ({x // x ∈ R} → B) :=
    { toFun := fun β r => β r.1
      map_add' := fun a b => rfl
      map_smul' := fun a b => rfl }
  -- A fixed point of `T` vanishing on `R` is identically zero: the relation
  -- `β q = c q • Φ (β (g q))` lets us propagate vanishing backwards along the `g`-orbits.
  have hker : ∀ β : Q → B, β ∈ LinearMap.ker (T - 1) → restr β = 0 → β = 0 := by
    intro β hβ hβ0
    have hfix : T β = β := by
      have h0 : (T - 1) β = 0 := LinearMap.mem_ker.mp hβ
      have : T β - β = 0 := by simpa using h0
      exact sub_eq_zero.mp this
    have hRzero : ∀ r ∈ R, β r = 0 := by
      intro r hr
      have := congrFun hβ0 ⟨r, hr⟩
      simpa [restr] using this
    -- vanishing is preserved when moving one step backwards along `g`
    have hstep : ∀ q, β (g q) = 0 → β q = 0 := by
      intro q hq
      have hq' : β q = c q • Φ (β (g q)) := by
        have h1 : β q = T β q := by rw [hfix]
        rw [h1, hT]
      rw [hq', hq, map_zero, smul_zero]
    -- hence it propagates along iterates
    have key : ∀ k q, β ((g ^ k) q) = 0 → β q = 0 := by
      intro k
      induction k with
      | zero => intro q h; simpa using h
      | succ k ih =>
        intro q h
        have h2 : β ((g ^ k) (g q)) = 0 := by
          rw [pow_succ] at h
          simpa using h
        exact hstep q (ih (g q) h2)
    funext q
    obtain ⟨k, hk⟩ := hR q
    exact key k q (hRzero _ hk)
  -- Consequently the restriction map is injective on the fixed space.
  have hinj : Function.Injective (restr.domRestrict (LinearMap.ker (T - 1))) := by
    intro x y hxy
    have hxy' : restr (x : Q → B) = restr (y : Q → B) := by
      simpa using hxy
    have hdiff : (x : Q → B) - (y : Q → B) ∈ LinearMap.ker (T - 1) :=
      (LinearMap.ker (T - 1)).sub_mem x.2 y.2
    have hz : (x : Q → B) - (y : Q → B) = 0 := by
      apply hker _ hdiff
      rw [map_sub, hxy', sub_self]
    exact Subtype.ext (sub_eq_zero.mp hz)
  calc Module.finrank K (LinearMap.ker (T - 1))
      ≤ Module.finrank K ({x // x ∈ R} → B) :=
        LinearMap.finrank_le_finrank_of_injective
          (f := restr.domRestrict (LinearMap.ker (T - 1))) hinj
    _ = R.card * Module.finrank K B := by
        rw [Module.finrank_pi_fintype]
        simp

end Work.HallHigman.GLCore
