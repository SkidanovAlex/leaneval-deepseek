import Mathlib
import Submission.Work.K3Inputs.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.K3Inputs

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

/-- **The affine product `𝔸ⁿ ×_{Spec 𝕜} 𝔸ᵐ ≅ 𝔸ⁿ⁺ᵐ`, over the base.**

`Work.K3Inputs.AffineN 𝕜 n = 𝔸(Fin n; Spec (.of 𝕜))` is Mathlib's
`AlgebraicGeometry.AffineSpace`, and `Work.K3.prodOver 𝕜 X Y = pullback (X ↘ Spec 𝕜) (Y ↘ Spec 𝕜)`
is the fibre product over `Spec 𝕜` (its `Over`-structure is the instance
`Work.K3.prodOverOver`).

Note `Work.K3.prodOver 𝕜 (AffineN 𝕜 n) (AffineN 𝕜 m)` is *definitionally*
`pullback (𝔸(Fin n; Spec 𝕜) ↘ Spec 𝕜) (𝔸(Fin m; Spec 𝕜) ↘ Spec 𝕜)`, and its structure morphism
`… ↘ Spec 𝕜` is definitionally `pullback.fst _ _ ≫ (𝔸(Fin n; Spec 𝕜) ↘ Spec 𝕜)`, so
`e.hom.IsOver (Spec (.of 𝕜))` unfolds (via `Hom.isOver_iff`) to
`e.hom ≫ (𝔸(Fin (n+m); Spec 𝕜) ↘ Spec 𝕜) = pullback.fst _ _ ≫ (𝔸(Fin n; Spec 𝕜) ↘ Spec 𝕜)`.

Suggested route: put `Q := pullback (𝔸(Fin n; Spec 𝕜) ↘ Spec 𝕜) (𝔸(Fin m; Spec 𝕜) ↘ Spec 𝕜)`.
* Forward `𝔸(Fin (n+m); Spec 𝕜) ⟶ Q` is `pullback.lift (AffineSpace.reindex Sum.inl _)
  (AffineSpace.reindex Sum.inr _) (by simp [AffineSpace.reindex_over])`.
* Inverse `Q ⟶ 𝔸(Fin (n+m); Spec 𝕜)` is `AffineSpace.homOfVector (Q ↘ Spec 𝕜) v` where
  `v : Fin (n+m) → Γ(Q, ⊤)` sends `k` to
  `Sum.elim (fun i : Fin n => (pullback.fst _ _).appTop (AffineSpace.coord _ i))
    (fun j : Fin m => (pullback.snd _ _).appTop (AffineSpace.coord _ j))
    ((finSumFinEquiv (m := n) (n := m)).symm k)`.
* `AffineSpace.homOfVector_over` / `homOfVector_appTop_coord` / `reindex_over` /
  `reindex_appTop_coord` compute the composites; `AffineSpace.hom_ext` and `pullback.hom_ext`
  discharge the two round trips (split `k : Fin (n+m)` via `finSumFinEquiv.surjective`).
Warning: `Work.K3.prodOver` is a semireducible `def`, so `rw`/`simp` cannot see through it —
restate goals with `show`/`change` in the explicit `pullback` form first. -/
theorem affineN_prodOver_iso (𝕜 : Type) [Field 𝕜] (n m : ℕ) :
    ∃ e : Work.K3.prodOver 𝕜 (Work.K3Inputs.AffineN 𝕜 n) (Work.K3Inputs.AffineN 𝕜 m) ≅
      Work.K3Inputs.AffineN 𝕜 (n + m),
      e.hom.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) := by
  -- Work with the explicit fibre product `Q` rather than the (semireducible) `prodOver`.
  let Q : Scheme.{0} := pullback (AffineN 𝕜 n ↘ Spec (CommRingCat.of 𝕜))
    (AffineN 𝕜 m ↘ Spec (CommRingCat.of 𝕜))
  -- `e : Fin n ⊕ Fin m ≃ Fin (n+m)`, `Sum.inl` first.
  let e : Fin n ⊕ Fin m ≃ Fin (n + m) := finSumFinEquiv (m := n) (n := m)
  -- The two projections `𝔸^{n+m} ⟶ 𝔸ⁿ`, `𝔸^{n+m} ⟶ 𝔸ᵐ` given by the reindexings.
  let p₁ : AffineN 𝕜 (n + m) ⟶ AffineN 𝕜 n :=
    AffineSpace.reindex (fun i => e (Sum.inl i)) (Spec (CommRingCat.of 𝕜))
  let p₂ : AffineN 𝕜 (n + m) ⟶ AffineN 𝕜 m :=
    AffineSpace.reindex (fun j => e (Sum.inr j)) (Spec (CommRingCat.of 𝕜))
  -- The two projections of the fibre product.
  let π₁ : Q ⟶ AffineN 𝕜 n := pullback.fst (AffineN 𝕜 n ↘ Spec (CommRingCat.of 𝕜))
    (AffineN 𝕜 m ↘ Spec (CommRingCat.of 𝕜))
  let π₂ : Q ⟶ AffineN 𝕜 m := pullback.snd (AffineN 𝕜 n ↘ Spec (CommRingCat.of 𝕜))
    (AffineN 𝕜 m ↘ Spec (CommRingCat.of 𝕜))
  have hp₁over : p₁ ≫ (AffineN 𝕜 n ↘ Spec (CommRingCat.of 𝕜)) =
      AffineN 𝕜 (n + m) ↘ Spec (CommRingCat.of 𝕜) := AffineSpace.reindex_over _ _
  have hp₂over : p₂ ≫ (AffineN 𝕜 m ↘ Spec (CommRingCat.of 𝕜)) =
      AffineN 𝕜 (n + m) ↘ Spec (CommRingCat.of 𝕜) := AffineSpace.reindex_over _ _
  -- The forward map `𝔸^{n+m} ⟶ Q`.
  let f : AffineN 𝕜 (n + m) ⟶ Q := pullback.lift p₁ p₂ (by rw [hp₁over, hp₂over])
  have hf₁ : f ≫ π₁ = p₁ := pullback.lift_fst _ _ _
  have hf₂ : f ≫ π₂ = p₂ := pullback.lift_snd _ _ _
  -- The coordinates of the inverse: the coordinates of the two factors.
  let v : Fin (n + m) → Γ(Q, ⊤) := fun k =>
    Sum.elim (fun i : Fin n => π₁.appTop (AffineSpace.coord (Spec (CommRingCat.of 𝕜)) i))
      (fun j : Fin m => π₂.appTop (AffineSpace.coord (Spec (CommRingCat.of 𝕜)) j))
      (e.symm k)
  -- The inverse map `Q ⟶ 𝔸^{n+m}`.
  let g : Q ⟶ AffineN 𝕜 (n + m) :=
    AffineSpace.homOfVector (π₁ ≫ (AffineN 𝕜 n ↘ Spec (CommRingCat.of 𝕜))) v
  have hgv : ∀ k, g.appTop (AffineSpace.coord (Spec (CommRingCat.of 𝕜)) k) = v k := fun k =>
    AffineSpace.homOfVector_appTop_coord _ _ k
  have hgov : g ≫ (AffineN 𝕜 (n + m) ↘ Spec (CommRingCat.of 𝕜)) =
      π₁ ≫ (AffineN 𝕜 n ↘ Spec (CommRingCat.of 𝕜)) := AffineSpace.homOfVector_over _ _
  have hp₁c : ∀ i, p₁.appTop (AffineSpace.coord (Spec (CommRingCat.of 𝕜)) i) =
      AffineSpace.coord (Spec (CommRingCat.of 𝕜)) (e (Sum.inl i)) :=
    fun i => AffineSpace.reindex_appTop_coord _ _ i
  have hp₂c : ∀ j, p₂.appTop (AffineSpace.coord (Spec (CommRingCat.of 𝕜)) j) =
      AffineSpace.coord (Spec (CommRingCat.of 𝕜)) (e (Sum.inr j)) :=
    fun j => AffineSpace.reindex_appTop_coord _ _ j
  have hv₁ : ∀ i, v (e (Sum.inl i)) = π₁.appTop (AffineSpace.coord (Spec (CommRingCat.of 𝕜)) i) := by
    intro i; simp only [v, Equiv.symm_apply_apply, Sum.elim_inl]
  have hv₂ : ∀ j, v (e (Sum.inr j)) = π₂.appTop (AffineSpace.coord (Spec (CommRingCat.of 𝕜)) j) := by
    intro j; simp only [v, Equiv.symm_apply_apply, Sum.elim_inr]
  -- `g` is a section of `p₁`: `g ≫ p₁ = π₁`.
  have hg₁ : g ≫ p₁ = π₁ := by
    refine AffineSpace.hom_ext ?_ ?_
    · show (g ≫ p₁) ≫ (AffineN 𝕜 n ↘ Spec (CommRingCat.of 𝕜)) =
          π₁ ≫ (AffineN 𝕜 n ↘ Spec (CommRingCat.of 𝕜))
      rw [Category.assoc, hp₁over, hgov]
    · intro i
      calc (g ≫ p₁).appTop (AffineSpace.coord (Spec (CommRingCat.of 𝕜)) i)
          = g.appTop (p₁.appTop (AffineSpace.coord (Spec (CommRingCat.of 𝕜)) i)) := by
            simp only [Hom.comp_appTop, CommRingCat.comp_apply]
        _ = g.appTop (AffineSpace.coord (Spec (CommRingCat.of 𝕜)) (e (Sum.inl i))) := by rw [hp₁c i]
        _ = v (e (Sum.inl i)) := by rw [hgv]
        _ = π₁.appTop (AffineSpace.coord (Spec (CommRingCat.of 𝕜)) i) := hv₁ i
  -- `g` is a section of `p₂`: `g ≫ p₂ = π₂`.
  have hg₂ : g ≫ p₂ = π₂ := by
    refine AffineSpace.hom_ext ?_ ?_
    · show (g ≫ p₂) ≫ (AffineN 𝕜 m ↘ Spec (CommRingCat.of 𝕜)) =
          π₂ ≫ (AffineN 𝕜 m ↘ Spec (CommRingCat.of 𝕜))
      rw [Category.assoc, hp₂over, hgov]
      exact pullback.condition
    · intro j
      calc (g ≫ p₂).appTop (AffineSpace.coord (Spec (CommRingCat.of 𝕜)) j)
          = g.appTop (p₂.appTop (AffineSpace.coord (Spec (CommRingCat.of 𝕜)) j)) := by
            simp only [Hom.comp_appTop, CommRingCat.comp_apply]
        _ = g.appTop (AffineSpace.coord (Spec (CommRingCat.of 𝕜)) (e (Sum.inr j))) := by rw [hp₂c j]
        _ = v (e (Sum.inr j)) := by rw [hgv]
        _ = π₂.appTop (AffineSpace.coord (Spec (CommRingCat.of 𝕜)) j) := hv₂ j
  -- First round trip: `g ≫ f = 𝟙 Q`.
  have hgf : g ≫ f = 𝟙 Q := by
    refine pullback.hom_ext ?_ ?_
    · show (g ≫ f) ≫ π₁ = 𝟙 Q ≫ π₁
      rw [Category.assoc, hf₁, hg₁, Category.id_comp]
    · show (g ≫ f) ≫ π₂ = 𝟙 Q ≫ π₂
      rw [Category.assoc, hf₂, hg₂, Category.id_comp]
  -- Second round trip: `f ≫ g = 𝟙 𝔸^{n+m}` (checked on the coordinates).
  have hfg : f ≫ g = 𝟙 (AffineN 𝕜 (n + m)) := by
    refine AffineSpace.hom_ext ?_ ?_
    · show (f ≫ g) ≫ (AffineN 𝕜 (n + m) ↘ Spec (CommRingCat.of 𝕜)) =
          𝟙 (AffineN 𝕜 (n + m)) ≫ (AffineN 𝕜 (n + m) ↘ Spec (CommRingCat.of 𝕜))
      rw [Category.assoc, hgov, ← Category.assoc, hf₁, hp₁over, Category.id_comp]
    · intro k
      obtain ⟨k', rfl⟩ := e.surjective k
      rcases k' with i | j
      · show (f ≫ g).appTop (AffineSpace.coord (Spec (CommRingCat.of 𝕜)) (e (Sum.inl i))) =
            AffineSpace.coord (Spec (CommRingCat.of 𝕜)) (e (Sum.inl i))
        calc (f ≫ g).appTop (AffineSpace.coord (Spec (CommRingCat.of 𝕜)) (e (Sum.inl i)))
            = f.appTop (g.appTop (AffineSpace.coord (Spec (CommRingCat.of 𝕜)) (e (Sum.inl i)))) := by
              simp only [Hom.comp_appTop, CommRingCat.comp_apply]
          _ = f.appTop (v (e (Sum.inl i))) := by rw [hgv]
          _ = f.appTop (π₁.appTop (AffineSpace.coord (Spec (CommRingCat.of 𝕜)) i)) := by rw [hv₁ i]
          _ = (f ≫ π₁).appTop (AffineSpace.coord (Spec (CommRingCat.of 𝕜)) i) := by
              simp only [Hom.comp_appTop, CommRingCat.comp_apply]
          _ = p₁.appTop (AffineSpace.coord (Spec (CommRingCat.of 𝕜)) i) := by rw [hf₁]
          _ = AffineSpace.coord (Spec (CommRingCat.of 𝕜)) (e (Sum.inl i)) := hp₁c i
      · show (f ≫ g).appTop (AffineSpace.coord (Spec (CommRingCat.of 𝕜)) (e (Sum.inr j))) =
            AffineSpace.coord (Spec (CommRingCat.of 𝕜)) (e (Sum.inr j))
        calc (f ≫ g).appTop (AffineSpace.coord (Spec (CommRingCat.of 𝕜)) (e (Sum.inr j)))
            = f.appTop (g.appTop (AffineSpace.coord (Spec (CommRingCat.of 𝕜)) (e (Sum.inr j)))) := by
              simp only [Hom.comp_appTop, CommRingCat.comp_apply]
          _ = f.appTop (v (e (Sum.inr j))) := by rw [hgv]
          _ = f.appTop (π₂.appTop (AffineSpace.coord (Spec (CommRingCat.of 𝕜)) j)) := by rw [hv₂ j]
          _ = (f ≫ π₂).appTop (AffineSpace.coord (Spec (CommRingCat.of 𝕜)) j) := by
              simp only [Hom.comp_appTop, CommRingCat.comp_apply]
          _ = p₂.appTop (AffineSpace.coord (Spec (CommRingCat.of 𝕜)) j) := by rw [hf₂]
          _ = AffineSpace.coord (Spec (CommRingCat.of 𝕜)) (e (Sum.inr j)) := hp₂c j
  refine ⟨Iso.mk g f hgf hfg, ?_⟩
  rw [Hom.isOver_iff]
  exact hgov

end Work.K3Inputs
