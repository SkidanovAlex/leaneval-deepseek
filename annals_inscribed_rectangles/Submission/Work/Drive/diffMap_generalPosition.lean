import Mathlib

/-!
# General position of the difference map of three linear maps `ℝ² → ℝ³`

For three linear maps `α 0, α 1, α 2 : ℝ² → ℝ³` consider the *difference map*

> `Φ (e₀, e₁, e₂) = (α 1 e₁ - α 0 e₀, α 2 e₂ - α 0 e₀)`

from `(ℝ²)³` to `ℝ³ × ℝ³`.  Both spaces have dimension `6`, and the theorem below identifies the
surjectivity of `Φ` with the *general position* of the triple `(α 0, α 1, α 2)`:

* `Φ` is onto **iff** all three maps are injective and their ranges meet only in `0`.

The forward implication is the rank–nullity count.  The backward implication is the elementary
statement that `Φ e = 0` forces `α 0 e₀ = α 1 e₁ = α 2 e₂` to lie in the triple intersection of the
ranges, hence to vanish; injectivity then kills `e`.

This is the `2`-dimensional analogue of the transversality criterion of three `3`-chains
(`Work.Drive.TripleTransverse`), stated for the concrete dimensions occurring here.
-/

namespace Work.Drive

/-- The difference map `(e₀, e₁, e₂) ↦ (α 1 e₁ - α 0 e₀, α 2 e₂ - α 0 e₀)` as a linear map. -/
private noncomputable def diffMap
    (α : Fin 3 → (EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3))) :
    (Fin 3 → EuclideanSpace ℝ (Fin 2)) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :=
  (((α 1).comp (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => EuclideanSpace ℝ (Fin 2)) 1) -
      (α 0).comp (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => EuclideanSpace ℝ (Fin 2)) 0)).prod
    ((α 2).comp (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => EuclideanSpace ℝ (Fin 2)) 2) -
      (α 0).comp (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => EuclideanSpace ℝ (Fin 2)) 0)))

private lemma diffMap_apply
    (α : Fin 3 → (EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)))
    (e : Fin 3 → EuclideanSpace ℝ (Fin 2)) :
    diffMap α e = (α 1 (e 1) - α 0 (e 0), α 2 (e 2) - α 0 (e 0)) := rfl

private lemma diffMap_eq_zero_iff
    (α : Fin 3 → (EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)))
    (e : Fin 3 → EuclideanSpace ℝ (Fin 2)) :
    diffMap α e = 0 ↔ α 1 (e 1) = α 0 (e 0) ∧ α 2 (e 2) = α 0 (e 0) := by
  rw [diffMap_apply]
  constructor
  · intro h
    have h1 : α 1 (e 1) - α 0 (e 0) = 0 := by simpa using congrArg Prod.fst h
    have h2 : α 2 (e 2) - α 0 (e 0) = 0 := by simpa using congrArg Prod.snd h
    exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩
  · rintro ⟨h1, h2⟩
    simp only [h1, h2, sub_self]
    rfl

theorem diffMap_generalPosition
    (α : Fin 3 → (EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3))) :
    Function.Surjective (fun e : Fin 3 → EuclideanSpace ℝ (Fin 2) =>
        ((α 1 (e 1) - α 0 (e 0) : EuclideanSpace ℝ (Fin 3)),
         (α 2 (e 2) - α 0 (e 0) : EuclideanSpace ℝ (Fin 3)))) ↔
      (∀ k, Function.Injective (α k)) ∧
        (LinearMap.range (α 0) ⊓ LinearMap.range (α 1) ⊓ LinearMap.range (α 2) = ⊥) := by
  have hdim : Module.finrank ℝ (Fin 3 → EuclideanSpace ℝ (Fin 2)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) := by
    rw [Module.finrank_pi_fintype, Module.finrank_prod]
    simp
  change Function.Surjective (diffMap α) ↔ _
  constructor
  · intro hsurj
    have hinjΦ : Function.Injective (diffMap α) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
    have hker : ∀ e : Fin 3 → EuclideanSpace ℝ (Fin 2), diffMap α e = 0 → e = 0 := by
      intro e he
      exact hinjΦ (by rw [he, map_zero])
    refine ⟨?_, ?_⟩
    · -- injectivity of the three maps from a vector supported in one coordinate
      have inj0 : Function.Injective (α 0) := by
        intro u v huv
        have hz : diffMap α (![u - v, (0 : EuclideanSpace ℝ (Fin 2)), 0] :
            Fin 3 → EuclideanSpace ℝ (Fin 2)) = 0 := by
          rw [diffMap_eq_zero_iff]
          refine ⟨?_, ?_⟩ <;> simp [map_sub, huv]
        have h : u - v = 0 := by simpa using congrFun (hker _ hz) 0
        exact sub_eq_zero.mp h
      have inj1 : Function.Injective (α 1) := by
        intro u v huv
        have hz : diffMap α (![(0 : EuclideanSpace ℝ (Fin 2)), u - v, 0] :
            Fin 3 → EuclideanSpace ℝ (Fin 2)) = 0 := by
          rw [diffMap_eq_zero_iff]
          refine ⟨?_, ?_⟩ <;> simp [map_sub, huv]
        have h : u - v = 0 := by simpa using congrFun (hker _ hz) 1
        exact sub_eq_zero.mp h
      have inj2 : Function.Injective (α 2) := by
        intro u v huv
        have hz : diffMap α (![(0 : EuclideanSpace ℝ (Fin 2)), 0, u - v] :
            Fin 3 → EuclideanSpace ℝ (Fin 2)) = 0 := by
          rw [diffMap_eq_zero_iff]
          refine ⟨?_, ?_⟩ <;> simp [map_sub, huv]
        have h : u - v = 0 := by simpa using congrFun (hker _ hz) 2
        exact sub_eq_zero.mp h
      intro k
      fin_cases k
      · exact inj0
      · exact inj1
      · exact inj2
    · -- the triple intersection of the ranges is trivial
      rw [Submodule.eq_bot_iff]
      intro y hy
      rw [Submodule.mem_inf, Submodule.mem_inf] at hy
      obtain ⟨⟨hy0, hy1⟩, hy2⟩ := hy
      obtain ⟨v0, hv0⟩ := LinearMap.mem_range.mp hy0
      obtain ⟨v1, hv1⟩ := LinearMap.mem_range.mp hy1
      obtain ⟨v2, hv2⟩ := LinearMap.mem_range.mp hy2
      have hz : diffMap α (![v0, v1, v2] : Fin 3 → EuclideanSpace ℝ (Fin 2)) = 0 := by
        rw [diffMap_eq_zero_iff]
        refine ⟨?_, ?_⟩ <;> simp [hv0, hv1, hv2]
      have h0 : (![v0, v1, v2] : Fin 3 → EuclideanSpace ℝ (Fin 2)) 0 = 0 :=
        congrFun (hker _ hz) 0
      have hv00 : v0 = 0 := by simpa using h0
      rw [← hv0, hv00, map_zero]
  · rintro ⟨hinj, htriple⟩
    have hker : LinearMap.ker (diffMap α) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro e he
      rw [LinearMap.mem_ker] at he
      obtain ⟨h1, h2⟩ := (diffMap_eq_zero_iff α e).mp he
      have hy : α 0 (e 0) ∈
          LinearMap.range (α 0) ⊓ LinearMap.range (α 1) ⊓ LinearMap.range (α 2) := by
        rw [Submodule.mem_inf, Submodule.mem_inf]
        exact ⟨⟨⟨e 0, rfl⟩, ⟨e 1, h1⟩⟩, ⟨e 2, h2⟩⟩
      rw [htriple, Submodule.mem_bot] at hy
      have h0 : e 0 = 0 := hinj 0 (by rw [hy, map_zero])
      have h1' : e 1 = 0 := hinj 1 (by rw [h1, hy, map_zero])
      have h2' : e 2 = 0 := hinj 2 (by rw [h2, hy, map_zero])
      funext i
      fin_cases i
      · simpa using h0
      · simpa using h1'
      · simpa using h2'
    have hinjΦ : Function.Injective (diffMap α) := LinearMap.ker_eq_bot.mp hker
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinjΦ

end Work.Drive
