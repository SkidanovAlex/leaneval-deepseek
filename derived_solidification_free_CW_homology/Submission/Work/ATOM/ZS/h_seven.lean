import Mathlib
import Submission.Work.ATOM.ZS.NullSeqMaps

open CategoryTheory Limits MonoidalCategory MonoidalClosed LightCondensed LightProfinite

namespace Work.ATOM

/-- **`(0,-) : T ⟶ (ℕ∪{∞}) ⊗ T`**, the section `t ↦ (0,t)` of the projection `(k,t) ↦ t`, written
as `(λ_ T).inv ≫ (ptAt 0 ▷ T)`: the left unitor of the cartesian monoidal structure on
`LightProfinite` is the second projection, so its inverse is `t ↦ (unit,t)`, and whiskering
`ptAt 0` sends `unit` to `0`.  This is the map whose `zmap` is the section used in the proof of
`h₇`. -/
noncomputable def dZero (T : LightProfinite.{0}) : T ⟶ (ℕ∪{∞}) ⊗ T :=
  (λ_ T).inv ≫ (ptAt (((0 : ℕ) : ℕ∪{∞})) ▷ T)

/-- `dZero T` is the pairing `⟨(0,-), id⟩` of the cartesian monoidal structure. -/
lemma dZero_eq_lift (T : LightProfinite.{0}) :
    dZero T = CartesianMonoidalCategory.lift
      (SemiCartesianMonoidalCategory.toUnit T ≫ ptAt (((0 : ℕ) : ℕ∪{∞}))) (𝟙 T) := by
  rw [dZero, show (λ_ T).inv = CartesianMonoidalCategory.lift
      (SemiCartesianMonoidalCategory.toUnit T) (𝟙 T) from by
    ext; simp [CartesianMonoidalCategory.leftUnitor_inv_snd]]
  rw [CartesianMonoidalCategory.lift_whiskerRight]

/-- The underlying function of `dZero`: `t ↦ (0,t)`. -/
lemma dZero_apply (t : ↥(ℕ∪{∞})) :
    dZero (ℕ∪{∞}) t = ((((0 : ℕ) : ℕ∪{∞})), t) := by
  rw [dZero_eq_lift]
  rfl

end Work.ATOM

namespace Work.ATOM.ZS

/-- `zmap` preserves identities. -/
lemma zmap_one (T : LightProfinite.{0}) :
    Work.ATOM.zmap (𝟙 T) = 𝟙 (Work.ATOM.zfree T) := by
  simp [Work.ATOM.zmap]

/-- **The description of the composite of `zmap dZero` with `EA`.**  The map
`(λ_ (ℤ[T])).inv ≫ (e₀ ▷ ℤ[T])`, which sends the basis vector `e_t` of `ℤ[T]` to `e₀ ⊗ e_t`, is
the composite of the section `zmap (dZero T) : ℤ[T] ⟶ ℤ[(ℕ∪{∞}) × T]` with the quotient
projection `EA T = μ⁻¹ ≫ (P_proj ▷ ℤ[T]) : ℤ[(ℕ∪{∞}) × T] ⟶ P ⊗ ℤ[T]`.

Proof: `dZero T = (λ_ T).inv ≫ (ptAt 0 ▷ T)`, and `map_leftUnitor_inv` computes
`F.map (λ_ T).inv = (λ_ (F.obj T)).inv ≫ ε ▷ F.obj T ≫ μ F 𝟙_ T` for any monoidal functor `F`
(here `F = lightProfiniteToLightCondSet ⋙ free ℤ`, with `ε = unitIso.hom` and
`μ = zfreeTensorIso`); the naturality of `μ` in its first variable (`μ_natural_left`) turns
`μ F 𝟙_ T ≫ F.map (ptAt 0 ▷ T)` into `F.map (ptAt 0) ▷ F.obj T ≫ μ F (ℕ∪{∞}) T`, and the latter
`μ F (ℕ∪{∞}) T = (zfreeTensorIso (ℕ∪{∞}) T).hom` cancels against the `μ⁻¹` in `EA T`. -/
theorem i0_spec (T : LightProfinite.{0}) :
    Work.ATOM.zmap (Work.ATOM.dZero T) ≫ Work.ATOM.EA T =
      (λ_ (Work.ATOM.zfree T)).inv ≫ (Work.ATOM.e0 ▷ Work.ATOM.zfree T) := by
  have hμ := Functor.LaxMonoidal.μ_natural_left
    (F := lightProfiniteToLightCondSet ⋙ free ℤ) (X := 𝟙_ LightProfinite)
    (Y := ℕ∪{∞}) (ptAt (((0 : ℕ) : ℕ∪{∞}))) T
  have hkey : Functor.LaxMonoidal.μ (lightProfiniteToLightCondSet ⋙ free ℤ) (𝟙_ LightProfinite) T ≫
        (lightProfiniteToLightCondSet ⋙ free ℤ).map (ptAt (((0 : ℕ) : ℕ∪{∞})) ▷ T) ≫
        (Work.ATOM.zfreeTensorIso (ℕ∪{∞}) T).inv ≫
        (LightCondensed.P_proj ▷ Work.ATOM.zfree T) =
      ((lightProfiniteToLightCondSet ⋙ free ℤ).map (ptAt (((0 : ℕ) : ℕ∪{∞}))) ▷
          (lightProfiniteToLightCondSet ⋙ free ℤ).obj T) ≫
        (LightCondensed.P_proj ▷ Work.ATOM.zfree T) := by
    rw [← Category.assoc, ← hμ]
    rw [show Functor.LaxMonoidal.μ (lightProfiniteToLightCondSet ⋙ free ℤ) (ℕ∪{∞}) T =
        (Work.ATOM.zfreeTensorIso (ℕ∪{∞}) T).hom from rfl]
    rw [Category.assoc, Iso.hom_inv_id_assoc]
  rw [show Work.ATOM.dZero T =
      (λ_ T).inv ≫ ((Work.ATOM.ptAt (((0 : ℕ) : ℕ∪{∞}))) ▷ T) from rfl]
  simp only [Work.ATOM.zmap]
  rw [Functor.map_comp]
  rw [Work.ATOM.EA]
  rw [← Functor.LaxMonoidal.left_unitality_inv (lightProfiniteToLightCondSet ⋙ free ℤ) T]
  simp only [Category.assoc]
  rw [hkey]
  rw [Work.ATOM.e0]
  rw [MonoidalCategory.comp_whiskerRight, MonoidalCategory.comp_whiskerRight]
  rfl

/-- **`φ_P ∘ (0,-) = id`**: the map `dZero (ℕ∪{∞}) : (ℕ∪{∞}) ⟶ (ℕ∪{∞})²`, `t ↦ (0,t)` is a
section of `φ_P` (hence of `F_P` after projecting to `P`), because `0 ≤ n(j)` for every `j`. -/
theorem dZero_comp_phiP (S : LightProfinite.{0}) [Infinite S] :
    Work.ATOM.dZero (ℕ∪{∞}) ≫ Work.ATOM.phiP S = 𝟙 (ℕ∪{∞}) := by
  apply ConcreteCategory.hom_ext
  intro t
  rw [ConcreteCategory.comp_apply]
  rw [show (Work.ATOM.dZero (ℕ∪{∞})) t = ((((0 : ℕ) : ℕ∪{∞})), t) from Work.ATOM.dZero_apply t]
  rcases t with _ | j
  · exact Work.ATOM.phiP_some_infty S 0
  · exact Work.ATOM.phiP_some_some_of_le (S := S) (k := 0) (j := j) (Nat.zero_le _)

/-- `P_proj : ℤ[ℕ∪{∞}] ⟶ P` is the cokernel projection `P = cokernel P_map`, hence an
epimorphism (a cofork which is a colimit has epimorphic projection); `def P_proj` blocks instance
search, so the instance is recorded here. -/
lemma epi_P_proj : Epi LightCondensed.P_proj := by
  unfold LightCondensed.P_proj
  exact Cofork.IsColimit.epi (colimit.isColimit _)

/-- **Identity `h₇` of REFS/03 §1**: `s_P ≫ F_P = 𝟙 P`, i.e. `F_P ∘ s_P = id`.
On the generator `e_j`: `s_P(e_j) = e₀ ⊗ e_j` and `F_P(0,j) = e_j` because `0 ≤ n(j)`
(`Work.ATOM.phiP_some_some_of_le`).  In Lean: precompose with `LightCondensed.P_proj` and use
`Work.ATOM.FP_spec`, together with the description of `EApp ≫ s_P` as
`zmap (fun k => ((0:ℕ∪{∞}), k))`.

The route: `P_proj` is an epimorphism (i.e. `P` is the cokernel `ℤ[ℕ∪{∞}]/ℤ[∞]`), so it suffices
to show `P_proj ≫ s_P ≫ F_P = P_proj`.  Now `leftUnitor_inv_naturality` and `whisker_exchange`
compute `P_proj ≫ s_P = (λ_ (ℤ[ℕ∪{∞}])).inv ≫ (e₀ ▷ ℤ[ℕ∪{∞}]) ≫ (P ◁ P_proj)`, and
`i0_spec` identifies the first two factors with `zmap (dZero (ℕ∪{∞})) ≫ EA (ℕ∪{∞})`; folding in
`(P ◁ P_proj)` gives `EApp`.  Then `FP_spec` rewrites `EApp ≫ F_P = zmap φ_P ≫ P_proj`, and
`dZero_comp_phiP` (`φ_P ∘ (0,-) = id`) finishes. -/
theorem h_seven (S : LightProfinite.{0}) [Infinite S] :
    Work.ATOM.sP ≫ Work.ATOM.FP S = 𝟙 LightCondensed.P := by
  have : Epi LightCondensed.P_proj := epi_P_proj
  refine (cancel_epi LightCondensed.P_proj).mp ?_
  rw [Category.comp_id]
  have hB : (λ_ (Work.ATOM.zfree (ℕ∪{∞}))).inv ≫
        (Work.ATOM.e0 ▷ Work.ATOM.zfree (ℕ∪{∞})) =
      Work.ATOM.zmap (Work.ATOM.dZero (ℕ∪{∞})) ≫ Work.ATOM.EA (ℕ∪{∞}) :=
    (i0_spec (ℕ∪{∞})).symm
  have hA : LightCondensed.P_proj ≫ Work.ATOM.sP =
      (λ_ (Work.ATOM.zfree (ℕ∪{∞}))).inv ≫ (Work.ATOM.e0 ▷ Work.ATOM.zfree (ℕ∪{∞})) ≫
        (LightCondensed.P ◁ LightCondensed.P_proj) := by
    rw [Work.ATOM.sP, ← Category.assoc, leftUnitor_inv_naturality LightCondensed.P_proj,
      Category.assoc, whisker_exchange Work.ATOM.e0 LightCondensed.P_proj]
  have hAE : (λ_ (Work.ATOM.zfree (ℕ∪{∞}))).inv ≫ (Work.ATOM.e0 ▷ Work.ATOM.zfree (ℕ∪{∞})) ≫
        (LightCondensed.P ◁ LightCondensed.P_proj) =
      Work.ATOM.zmap (Work.ATOM.dZero (ℕ∪{∞})) ≫ Work.ATOM.EApp := by
    rw [← Category.assoc, hB, Category.assoc,
      show Work.ATOM.EA (ℕ∪{∞}) ≫ (LightCondensed.P ◁ LightCondensed.P_proj) =
        Work.ATOM.EApp from rfl]
  calc LightCondensed.P_proj ≫ Work.ATOM.sP ≫ Work.ATOM.FP S
      = (LightCondensed.P_proj ≫ Work.ATOM.sP) ≫ Work.ATOM.FP S := (Category.assoc _ _ _).symm
    _ = ((λ_ (Work.ATOM.zfree (ℕ∪{∞}))).inv ≫ (Work.ATOM.e0 ▷ Work.ATOM.zfree (ℕ∪{∞})) ≫
          (LightCondensed.P ◁ LightCondensed.P_proj)) ≫ Work.ATOM.FP S := by rw [hA]
    _ = (Work.ATOM.zmap (Work.ATOM.dZero (ℕ∪{∞})) ≫ Work.ATOM.EApp) ≫ Work.ATOM.FP S := by
          rw [hAE]
    _ = Work.ATOM.zmap (Work.ATOM.dZero (ℕ∪{∞})) ≫ Work.ATOM.EApp ≫ Work.ATOM.FP S :=
          Category.assoc _ _ _
    _ = Work.ATOM.zmap (Work.ATOM.dZero (ℕ∪{∞})) ≫ Work.ATOM.FPsection S := by
          rw [Work.ATOM.FP_spec]
    _ = Work.ATOM.zmap (Work.ATOM.dZero (ℕ∪{∞})) ≫ Work.ATOM.zmap (Work.ATOM.phiP S) ≫
          LightCondensed.P_proj := rfl
    _ = Work.ATOM.zmap (Work.ATOM.dZero (ℕ∪{∞}) ≫ Work.ATOM.phiP S) ≫ LightCondensed.P_proj := by
          rw [zmap_comp, Category.assoc]
    _ = LightCondensed.P_proj := by
          rw [dZero_comp_phiP S, zmap_one, Category.id_comp]

end Work.ATOM.ZS
