import Mathlib
import Submission.Work.TOOLKIT.SeqColim.Defs

open CategoryTheory Limits

namespace Work.TOOLKIT.SeqColim

open Work.TOOLKIT

/-! ## Naturality of the shift

`Sigma.map (fun n => τ.app n)` commutes with the shift maps, because `τ` is natural at the
transition maps.  Both squares defining the morphism of telescope short complexes are immediate
consequences; the second one additionally uses the naturality of the colimit cocone. -/

/-- Naturality of the coproduct of the transition maps against the shift: for a natural
transformation `τ : F ⟶ G` of sequential diagrams, the coproduct map `∐_n τ_n` intertwines the
shift of `F` with the shift of `G`. -/
lemma Sigma_map_towerShift_step (F G : ℕ ⥤ Cpx) (τ : F ⟶ G) :
    Limits.Sigma.map (fun n => τ.app n) ≫ towerShift (fun n => G.obj n) (step G) =
      towerShift (fun n => F.obj n) (step F) ≫ Limits.Sigma.map (fun n => τ.app n) := by
  apply Limits.Sigma.hom_ext
  intro k
  have hL : Limits.Sigma.ι (fun n => F.obj n) k ≫
      (Limits.Sigma.map (fun n => τ.app n) ≫ towerShift (fun n => G.obj n) (step G)) =
      τ.app k ≫ step G k ≫ Limits.Sigma.ι (fun n => G.obj n) (k+1) := by
    rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc, Sigma_ι_towerShift]
  have hR : Limits.Sigma.ι (fun n => F.obj n) k ≫
      (towerShift (fun n => F.obj n) (step F) ≫ Limits.Sigma.map (fun n => τ.app n)) =
      step F k ≫ τ.app (k+1) ≫ Limits.Sigma.ι (fun n => G.obj n) (k+1) := by
    rw [← Category.assoc, Sigma_ι_towerShift, Category.assoc, Limits.Sigma.ι_map]
  rw [hL, hR]
  dsimp only [step]
  rw [← Category.assoc]
  conv_rhs => rw [← Category.assoc]
  rw [← τ.naturality (homOfLE (Nat.le_succ k))]

/-- The morphism of telescope short complexes induced by a natural transformation of sequential
diagrams `τ : F ⟶ G`: there is `φ : telShort F ⟶ telShort G` whose first two components are the
coproduct `Sigma.map (fun n => τ.app n)` and whose third component is `colim.map τ`.

Route.  Use `ShortComplex.homMk` with `τ₁ = τ₂ = Sigma.map (fun n => τ.app n)` and
`τ₃ = colim.map τ`.  The two commutation squares are proved by `Sigma.hom_ext` (both sides are maps
out of the coproduct `∐_n F_n`):
* `Sigma.map (fun n => τ.app n) ≫ telD G = telD F ≫ Sigma.map (fun n => τ.app n)`: on the `k`-th
  summand use `Sigma.ι_map`, `Sigma_ι_towerD` and the naturality of `τ` at `homOfLE (Nat.le_succ k)`;
* `Sigma.map (fun n => τ.app n) ≫ toColim G = toColim F ≫ colim.map τ`: on the `k`-th summand use
  `Sigma.ι_map`, `Sigma_ι_toColim` (i.e. `Sigma.ι _ k ≫ toColim F = colimit.ι F k`) and
  `colimit.ι_map`.
The three component equalities are then `rfl`. -/
theorem exists_telShortMap (F G : CategoryTheory.Functor ℕ Work.TOOLKIT.Cpx) (τ : F ⟶ G) :
    ∃ φ : Work.TOOLKIT.SeqColim.telShort F ⟶ Work.TOOLKIT.SeqColim.telShort G,
      φ.τ₁ = CategoryTheory.Limits.Sigma.map (fun n => τ.app n) ∧
        φ.τ₂ = CategoryTheory.Limits.Sigma.map (fun n => τ.app n) ∧
          φ.τ₃ = CategoryTheory.Limits.colim.map τ := by
  have sq1 : Limits.Sigma.map (fun n => τ.app n) ≫ telD G =
      telD F ≫ Limits.Sigma.map (fun n => τ.app n) := by
    dsimp only [telD, towerD]
    rw [Preadditive.comp_sub, Category.comp_id, Sigma_map_towerShift_step, Preadditive.sub_comp,
      Category.id_comp]
  have sq2 : Limits.Sigma.map (fun n => τ.app n) ≫ toColim G = toColim F ≫ colim.map τ := by
    apply Limits.Sigma.hom_ext
    intro k
    have hL : Limits.Sigma.ι (fun n => F.obj n) k ≫
        (Limits.Sigma.map (fun n => τ.app n) ≫ toColim G) = τ.app k ≫ colimit.ι G k := by
      rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc, Sigma_ι_toColim]
    have hR : Limits.Sigma.ι (fun n => F.obj n) k ≫ (toColim F ≫ colim.map τ) =
        τ.app k ≫ colimit.ι G k := by
      rw [← Category.assoc, Sigma_ι_toColim, colimit.ι_map]
    rw [hL, hR]
  exact ⟨ShortComplex.homMk (Limits.Sigma.map (fun n => τ.app n))
    (Limits.Sigma.map (fun n => τ.app n)) (colim.map τ) sq1 sq2, rfl, rfl, rfl⟩

end Work.TOOLKIT.SeqColim
