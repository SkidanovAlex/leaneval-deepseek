import Mathlib
import Submission.Work.Drive.TripleGeneral

/-!
# Transversality of the three "block" derivative maps

Suppose `π : ℝ³ → ℝ²` and `τ : ℝ³ → ℝ` are linear, that `τ` is nonzero on `ker π` and that
`π` maps the kernel of `τ` onto `ℝ²` (so that `π` and `τ` are "independent" and every pair
`(y,t) ∈ ℝ² × ℝ` is realised by some `v ∈ ℝ³` with `π v = y`, `τ v = t`).

For three injective linear maps `c k : ℝ² → ℝ³` whose ranges meet only in `0`, and arbitrary
linear maps `b k : ℝ² → ℝ` and nonzero scalars `a k`, the three linear maps

> `f k = ((b k) ∘ π + (a k) • τ) × ((c k) ∘ π) : ℝ³ → ℝ × ℝ³`

are in general position: the difference map `(v₀,v₁,v₂) ↦ (f₀v₀ - f₁v₁, f₀v₀ - f₂v₂)` is onto.
This is the `E = ℝ × ℝ³` instance of `Work.Drive.TripleTransverseE`.

The proof is elementary linear algebra.  Solving first the `ℝ³`-valued equations
`c₀x₀ - c₁x₁ = y₁`, `c₀x₀ - c₂x₂ = y₂` is possible because the map
`(x₀,x₁,x₂) ↦ (c₀x₀ - c₁x₁, c₀x₀ - c₂x₂)` is injective (its kernel forces
`c₀x₀ ∈ range c₀ ⊓ range c₁ ⊓ range c₂ = 0`) between spaces of equal dimension `6`;
the remaining scalar equations are then solved by the free `τ`-coordinates, using `a k ≠ 0`.
-/

namespace Work.Drive

open scoped Manifold ContDiff

noncomputable section

/-- The parameter space `ℝ²` of the blocks. -/
abbrev BlockY := EuclideanSpace ℝ (Fin 2)

/-- The target space `ℝ³` of the blocks. -/
abbrev BlockX := EuclideanSpace ℝ (Fin 3)

/-- **Solving the three blocks in the `ℝ³` coordinate.**  For three injective linear maps
`c k : ℝ² → ℝ³` with `range c₀ ⊓ range c₁ ⊓ range c₂ = ⊥` and any `y₁ y₂ : ℝ³` there are
`x₀ x₁ x₂ : ℝ²` with `c₀x₀ - c₁x₁ = y₁` and `c₀x₀ - c₂x₂ = y₂`. -/
theorem exists_block_solution
    (c : Fin 3 → BlockY →L[ℝ] BlockX)
    (hc : ∀ k, Function.Injective (c k))
    (hV : (c 0).range ⊓ (c 1).range ⊓ (c 2).range = ⊥)
    (y₁ y₂ : BlockX) :
    ∃ x : BlockY × BlockY × BlockY,
      c 0 x.1 - c 1 x.2.1 = y₁ ∧ c 0 x.1 - c 2 x.2.2 = y₂ := by
  let L : (BlockY × BlockY × BlockY) →ₗ[ℝ] BlockX × BlockX :=
    (((c 0).toLinearMap.comp (LinearMap.fst ℝ BlockY (BlockY × BlockY))) -
        ((c 1).toLinearMap.comp
          ((LinearMap.fst ℝ BlockY BlockY).comp (LinearMap.snd ℝ BlockY (BlockY × BlockY))))).prod
      (((c 0).toLinearMap.comp (LinearMap.fst ℝ BlockY (BlockY × BlockY))) -
        ((c 2).toLinearMap.comp
          ((LinearMap.snd ℝ BlockY BlockY).comp (LinearMap.snd ℝ BlockY (BlockY × BlockY)))))
  have hL : ∀ x : BlockY × BlockY × BlockY,
      L x = (c 0 x.1 - c 1 x.2.1, c 0 x.1 - c 2 x.2.2) := by
    intro x
    simp [L]
  have hdim : Module.finrank ℝ (BlockY × BlockY × BlockY) =
      Module.finrank ℝ (BlockX × BlockX) := by
    simp [Module.finrank_prod, finrank_euclideanSpace]
  have hker : ∀ x : BlockY × BlockY × BlockY, L x = 0 → x = 0 := by
    intro x hx
    rw [hL x] at hx
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hx
    have e1 : c 0 x.1 = c 1 x.2.1 := sub_eq_zero.mp h1
    have e2 : c 0 x.1 = c 2 x.2.2 := sub_eq_zero.mp h2
    have hmem : c 0 x.1 ∈ (c 0).range ⊓ (c 1).range ⊓ (c 2).range := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact ⟨x.1, rfl⟩
      · exact ⟨x.2.1, e1.symm⟩
      · exact ⟨x.2.2, e2.symm⟩
    rw [hV] at hmem
    have h0 : c 0 x.1 = 0 := by simpa using hmem
    have hx0 : x.1 = 0 := hc 0 (by rw [h0, map_zero])
    have hx1 : x.2.1 = 0 := hc 1 (by rw [← e1, h0, map_zero])
    have hx2 : x.2.2 = 0 := hc 2 (by rw [← e2, h0, map_zero])
    exact Prod.ext hx0 (Prod.ext hx1 hx2)
  have hkerbot : L.ker = ⊥ := (LinearMap.ker_eq_bot' (f := L)).mpr hker
  have hinj : Function.Injective L := LinearMap.ker_eq_bot.mp hkerbot
  have hsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  obtain ⟨x, hx⟩ := hsurj (y₁, y₂)
  refine ⟨x, ?_, ?_⟩
  · have := congrArg Prod.fst hx; simpa [hL x] using this
  · have := congrArg Prod.snd hx; simpa [hL x] using this

/-- **Realising prescribed `π`- and `τ`-values.**  If `τ` is nonzero on `ker π` and the kernel of
`τ` surjects onto `ℝ²` under `π`, then every `(y,t) ∈ ℝ² × ℝ` is `(π v, τ v)` for some `v`. -/
theorem exists_pi_tau_lift
    (π : BlockX →L[ℝ] BlockY) (τ : BlockX →L[ℝ] ℝ)
    (hker : ∃ w : BlockX, π w = 0 ∧ τ w ≠ 0)
    (hsplit : ∀ y : BlockY, ∃ v : BlockX, τ v = 0 ∧ π v = y)
    (y : BlockY) (t : ℝ) : ∃ v : BlockX, π v = y ∧ τ v = t := by
  obtain ⟨w, hwπ, hwτ⟩ := hker
  obtain ⟨u, huτ, huπ⟩ := hsplit y
  refine ⟨u + (t / τ w) • w, ?_, ?_⟩
  · simp only [map_add, huπ, map_smul, hwπ, smul_zero, add_zero]
  · simp only [map_add, huτ, map_smul, smul_eq_mul, zero_add]
    exact div_mul_cancel₀ t hwτ

theorem tripleTransverseE_of_blocks
    (π : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (τ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (hker : ∃ w : EuclideanSpace ℝ (Fin 3), π w = 0 ∧ τ w ≠ 0)
    (hsplit : ∀ y : EuclideanSpace ℝ (Fin 2), ∃ v : EuclideanSpace ℝ (Fin 3), τ v = 0 ∧ π v = y)
    (a : Fin 3 → ℝ) (ha : ∀ k, a k ≠ 0)
    (b : Fin 3 → EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
    (c : Fin 3 → EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (hc : ∀ k, Function.Injective (c k))
    (hV : (c 0).range ⊓ (c 1).range ⊓ (c 2).range = ⊥) :
    Work.Drive.TripleTransverseE (((b 0).comp π + (a 0) • τ).prod ((c 0).comp π))
      (((b 1).comp π + (a 1) • τ).prod ((c 1).comp π))
      (((b 2).comp π + (a 2) • τ).prod ((c 2).comp π)) := by
  intro w₁ w₂
  obtain ⟨x, hx₁, hx₂⟩ := exists_block_solution c hc hV w₁.2 w₂.2
  obtain ⟨v₀, hπ₀, hτ₀⟩ := exists_pi_tau_lift π τ hker hsplit x.1 0
  obtain ⟨v₁, hπ₁, hτ₁⟩ :=
    exists_pi_tau_lift π τ hker hsplit x.2.1 ((b 0 x.1 - b 1 x.2.1 - w₁.1) / a 1)
  obtain ⟨v₂, hπ₂, hτ₂⟩ :=
    exists_pi_tau_lift π τ hker hsplit x.2.2 ((b 0 x.1 - b 2 x.2.2 - w₂.1) / a 2)
  have hf : ∀ (k : Fin 3) (v : BlockX),
      (((b k).comp π + (a k) • τ).prod ((c k).comp π)) v
        = (b k (π v) + a k * τ v, c k (π v)) := by
    intro k v
    simp only [ContinuousLinearMap.prod_apply, add_apply,
      ContinuousLinearMap.comp_apply, smul_apply, smul_eq_mul]
  let vv : Fin 3 → BlockX := ![v₀, v₁, v₂]
  have hv0 : vv 0 = v₀ := rfl
  have hv1 : vv 1 = v₁ := rfl
  have hv2 : vv 2 = v₂ := rfl
  refine ⟨vv, ?_, ?_⟩
  · rw [hv0, hv1, hf 0 v₀, hf 1 v₁, hπ₀, hπ₁, hτ₀, hτ₁]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_sub]
      rw [mul_zero, add_zero, mul_div_cancel₀ _ (ha 1)]
      ring
    · simp only [Prod.snd_sub]
      exact hx₁
  · rw [hv0, hv2, hf 0 v₀, hf 2 v₂, hπ₀, hπ₂, hτ₀, hτ₂]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_sub]
      rw [mul_zero, add_zero, mul_div_cancel₀ _ (ha 2)]
      ring
    · simp only [Prod.snd_sub]
      exact hx₂

end

end Work.Drive
