import Mathlib
import Submission.Work.TOOLKIT.Basic
import Submission.Work.TOOLKIT.Instances
import Submission.Work.TOOLKIT.Levelwise.Basic
import Submission.Work.TOOLKIT.Levelwise.Maps
import Submission.Work.TOOLKIT.Levelwise.Tower
import Submission.Work.TOOLKIT.Levelwise.TowerMap
import Submission.Work.TOOLKIT.Levelwise.SolidEquivBasic
import Submission.Work.TOOLKIT.Levelwise.truncSES_shortExact
import Submission.Work.TOOLKIT.Levelwise.exists_colimIso_truncTower
import Submission.Work.TOOLKIT.Levelwise.solidEquiv_sng_shift
import Submission.Work.TOOLKIT.Levelwise.solidEquiv_truncMap_zero_of

open CategoryTheory Limits
open _root_.LightCondensed _root_.LightCondensed.Solid
open Submission.Blueprint

namespace Work.TOOLKIT.Levelwise

/-- The degreewise criterion: for complexes `K`, `L` concentrated in degrees `≤ 0`, a map
`f : K ⟶ L` is a solid-equivalence as soon as each degreewise component `f.f q : K.X q ⟶ L.X q`,
viewed as a map of single complexes in degree `0`, is one.  Route: the brutal truncations
`T_m := σ^{≥-m}` satisfy the short exact sequences
`0 → T_{m-1}K → T_mK → K.X^{-m}[-m] → 0` (and similarly for `L`), so the middle rule `hSes`
(`τ₁ ∧ τ₃ ⇒ τ₂`) applied to the induced morphism of short exact sequences proves the statement for
`T_m f` by induction on `m` (using `hf` for the cokernel term, and that single complexes are
compatible with shifts); the truncations exhaust `K` along monomorphisms, so `hseqcolim` finishes
the argument. -/
theorem solidEquiv_levelwise_of
    (hSes : ∀ {S₁ S₂ : CategoryTheory.ShortComplex Work.TOOLKIT.Cpx}, S₁.ShortExact →
      S₂.ShortExact → (φ : S₁ ⟶ S₂) →
      Submission.Blueprint.SolidEquiv (DerivedCategory.Q.map φ.τ₁) →
      Submission.Blueprint.SolidEquiv (DerivedCategory.Q.map φ.τ₃) →
      Submission.Blueprint.SolidEquiv (DerivedCategory.Q.map φ.τ₂))
    (hseqcolim : ∀ (F G : CategoryTheory.Functor ℕ Work.TOOLKIT.Cpx) (τ : F ⟶ G)
      (hF : ∀ n, CategoryTheory.Mono (F.map (CategoryTheory.homOfLE (Nat.le_succ n))))
      (hG : ∀ n, CategoryTheory.Mono (G.map (CategoryTheory.homOfLE (Nat.le_succ n))))
      (_ : ∀ n, Submission.Blueprint.SolidEquiv (DerivedCategory.Q.map (τ.app n))),
      Submission.Blueprint.SolidEquiv
        (DerivedCategory.Q.map (CategoryTheory.Limits.colim.map τ)))
    (K L : Work.TOOLKIT.Cpx) (f : K ⟶ L)
    (hK : ∀ q : ℤ, 0 < q → CategoryTheory.Limits.IsZero (K.X q))
    (hL : ∀ q : ℤ, 0 < q → CategoryTheory.Limits.IsZero (L.X q))
    (hf : ∀ q : ℤ, Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map (f.f q))) :
    Submission.Blueprint.SolidEquiv (DerivedCategory.Q.map f) := by
  -- the truncation tower is a tower of monomorphisms
  have hmonoK : ∀ n : ℕ, Mono ((truncTower K).map (homOfLE (Nat.le_succ n))) := by
    intro n
    exact (truncSES_shortExact n K).mono_f
  have hmonoL : ∀ n : ℕ, Mono ((truncTower L).map (homOfLE (Nat.le_succ n))) := by
    intro n
    exact (truncSES_shortExact n L).mono_f
  -- each stage of the truncation tower is a solid-equivalence, by induction on the stage
  have hind : ∀ m : ℕ, SolidEquiv (DerivedCategory.Q.map (truncMap f (-(m : ℤ)))) := by
    intro m
    induction m with
    | zero => exact solidEquiv_truncMap_zero_of f hK hL (hf 0)
    | succ m ih =>
      have h1 : SolidEquiv (DerivedCategory.Q.map (truncSESMap f m).τ₁) := by
        rw [truncSESMap_τ₁]
        exact ih
      have h3 : SolidEquiv (DerivedCategory.Q.map (truncSESMap f m).τ₃) := by
        rw [truncSESMap_τ₃]
        exact solidEquiv_sng_shift (f.f (-(m + 1 : ℤ))) (-(m + 1 : ℤ)) (hf (-(m + 1 : ℤ)))
      have h2 := hSes (truncSES_shortExact m K) (truncSES_shortExact m L) (truncSESMap f m) h1 h3
      rwa [truncSESMap_τ₂] at h2
  -- the colimit of the tower computes `K` and `L`
  obtain ⟨eK, heK⟩ := exists_colimIso_truncTower K
  obtain ⟨eL, heL⟩ := exists_colimIso_truncTower L
  have hcolim : SolidEquiv (DerivedCategory.Q.map (colim.map (truncTowerMap f))) :=
    hseqcolim (truncTower K) (truncTower L) (truncTowerMap f) hmonoK hmonoL (fun m => hind m)
  -- the canonical square relating `f` to the colimit map
  have hsquare : eK.hom ≫ f = colim.map (truncTowerMap f) ≫ eL.hom := by
    apply colimit.hom_ext
    intro m
    rw [← Category.assoc, heK m, ← Category.assoc, colimit.ι_map, Category.assoc, heL m]
    show truncIntoK (-(m : ℤ)) K ≫ f = truncMap f (-(m : ℤ)) ≫ truncIntoK (-(m : ℤ)) L
    rw [truncMap_comp_truncIntoK]
  -- conclude by conjugating with the two isomorphisms
  have hconj := solidEquiv_iso_conj (DerivedCategory.Q.map eK.hom) (DerivedCategory.Q.map f)
    (DerivedCategory.Q.map eL.inv) (Functor.map_isIso DerivedCategory.Q eK.hom)
    (Functor.map_isIso DerivedCategory.Q eL.inv)
  refine hconj.mp ?_
  have hs' : (eK.hom ≫ f) ≫ eL.inv = colim.map (truncTowerMap f) := by
    rw [hsquare, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have heq : DerivedCategory.Q.map eK.hom ≫ DerivedCategory.Q.map f ≫
      DerivedCategory.Q.map eL.inv = DerivedCategory.Q.map (colim.map (truncTowerMap f)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun g => DerivedCategory.Q.map g) hs'
  rw [heq]
  exact hcolim


end Work.TOOLKIT.Levelwise
