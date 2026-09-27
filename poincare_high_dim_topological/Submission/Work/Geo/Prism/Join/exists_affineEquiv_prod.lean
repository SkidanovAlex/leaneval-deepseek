import Mathlib
import Submission.Work.PL.Defs

namespace Work.Geo.Prism.Join

/-- The "prism coordinates" affine equivalence: if `π : E n → E a` is linear with kernel `W`,
`a + dim W = n`, and `Z : E n →ᵃ[ℝ] F` is affine with `Z.linear` injective on `W` and
`dim F = dim W`, then `x ↦ (π (x - x₀), Z x)` is an affine equivalence `E n ≃ᵃ (E a × F)`. -/
lemma exists_affineEquiv_prod {n a : ℕ} (W : Submodule ℝ (PL.E n))
    (π : PL.E n →ₗ[ℝ] PL.E a) (hπ : π.ker = W) (hae : a + Module.finrank ℝ W = n)
    {F : Type*} [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    (Z : PL.E n →ᵃ[ℝ] F) (x₀ : PL.E n)
    (hZ : ∀ v ∈ W, Z.linear v = 0 → v = 0) (hF : Module.finrank ℝ F = Module.finrank ℝ W) :
    ∃ T : PL.E n ≃ᵃ[ℝ] (PL.E a × F), ∀ x, T x = (π (x -ᵥ x₀), Z x) := by
  let L : PL.E n →ₗ[ℝ] (PL.E a × F) := π.prod Z.linear
  have hL : ∀ x, L x = (π x, Z.linear x) := by
    intro x; rw [LinearMap.prod_apply]; rfl
  -- `π × Z.linear` is injective
  have hker : L.ker = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x hx
    rw [LinearMap.mem_ker] at hx
    have h1 : π x = 0 := by
      have := congrArg Prod.fst hx
      simpa [hL x] using this
    have h2 : Z.linear x = 0 := by
      have := congrArg Prod.snd hx
      simpa [hL x] using this
    exact hZ x (by rw [← hπ, LinearMap.mem_ker]; exact h1) h2
  have hinj : Function.Injective L := LinearMap.ker_eq_bot.mp hker
  -- dimensions agree
  have hdim : Module.finrank ℝ (PL.E n) = Module.finrank ℝ (PL.E a × F) := by
    rw [Module.finrank_prod]
    simp [finrank_euclideanSpace, hF, hae]
  have hsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  let Lₑ : PL.E n ≃ₗ[ℝ] (PL.E a × F) := LinearEquiv.ofBijective L ⟨hinj, hsurj⟩
  have hLₑ : ∀ x, Lₑ x = (π x, Z.linear x) := by
    intro x; exact hL x
  -- `Z` is the translate of its linear part along `x₀`
  have key : ∀ p' : PL.E n, Z p' = Z.linear (p' -ᵥ x₀) + Z x₀ := by
    intro p'
    have h := AffineMap.map_vadd Z x₀ (p' -ᵥ x₀)
    rw [vsub_vadd] at h
    simpa using h
  refine ⟨AffineEquiv.mk' (fun x => (π (x -ᵥ x₀), Z x)) Lₑ x₀ ?_, fun x => rfl⟩
  intro p'
  rw [hLₑ, key p']
  simp [vadd_eq_add]

end Work.Geo.Prism.Join
