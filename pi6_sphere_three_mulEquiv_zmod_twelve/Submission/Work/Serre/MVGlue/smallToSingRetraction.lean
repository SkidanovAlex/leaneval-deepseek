import Mathlib
import Submission.Work.Cohomology.smallChainsHomotopyEquiv
import Submission.Work.Cohomology.homotopyEquivOfRetract
import Submission.Work.Cohomology.existsSmallChainsContraction
import Submission.Work.Cohomology.smallProj_spec
import Submission.Work.Cohomology.exists_sub_small_of_boundary_small

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A *strict* chain-level retraction of the small chains

Let `X` be a topological space and `U`, `V ⊆ X` an open cover.  The inclusion of the small chains
`i = smallToSing U V : C^{U,V}_*(X) ⟶ C_*(X)` is a quasi-isomorphism (the small simplices theorem)
and in fact a chain homotopy equivalence (`Work.Cohomology.smallChainsHomotopyEquiv`), but the
homotopy inverse produced there is only an inverse *up to homotopy*.

This file proves the stronger statement that `i` is a **split monomorphism** of chain complexes:
there is a genuine chain map `v : C_*(X) ⟶ C^{U,V}_*(X)` with `i ≫ v = 𝟙`.

## The argument

It is a purely homological statement, proved in `exists_retraction_of_contraction`:

* `i` is a degreewise split mono, with chosen retraction `p` (`i.f n ≫ p n = 𝟙`);
* the complement of the small chains is *contracted*: there is `κ n : B.X n ⟶ B.X (n+1)` with
  `(p n ≫ i.f n) ≫ κ n = 0`, `κ n ≫ (p (n+1) ≫ i.f (n+1)) = 0` and
  `(κ (n+1) ≫ B.d (n+2) (n+1) + B.d (n+1) n ≫ κ n - 𝟙) ≫ (𝟙 - p (n+1) ≫ i.f (n+1)) = 0`
  (this is the data supplied by `Work.Cohomology.existsSmallChainsContraction`).

Writing `θₙ = i.f n ≫ p n` (so `𝟙 - θₙ` is the projection onto the complement), `B.d` for the
differential of `B` and `d` for that of `A`, the three identities give

* `i.f n ≫ κ n = 0`,            (from `h1`, because `i ≫ p = 𝟙`)
* `κ n ≫ p (n+1) = 0`,           (from `h2`, because `i` is a mono — indeed a split mono),
* `Eₙ ≫ θₙ = Eₙ` where `Eₙ = κ n ≫ B.d (n+1) n + B.d n (n-1) ≫ κ (n-1) - 𝟙`  (from `h3`).

Then, with `Λₙ = p n ≫ A.d n (n-1) - B.d n (n-1) ≫ p (n-1)` (the failure of `p` to be a chain
map) and the explicit correction `wₙ = κ n ≫ B.d (n+1) n ≫ p n`, one has `i.f n ≫ Λₙ = 0`, hence
`Eₙ ≫ Λₙ = Eₙ ≫ θₙ ≫ Λₙ = 0`, which is exactly the statement that `Λₙ` is the "homological
defect" cancelled by `w`:

  `κ (n+1) ≫ B.d (n+2) (n+1) ≫ Λ (n+1) = Λ (n+1) - B.d (n+1) n ≫ κ n ≫ Λ (n+1)`

(using `B.d (n+2) (n+1) ≫ B.d (n+1) n = 0`), and the identity

  `w (n+1) ≫ A.d (n+1) n - B.d (n+1) n ≫ w n = Λ (n+1)`

follows after substituting `p (n+1) ≫ A.d (n+1) n = Λ (n+1) + B.d (n+1) n ≫ p n` and
`κ n ≫ p (n+1) = 0`.  Therefore `v n := p n - w n` is a chain map, and `i.f n ≫ v n = 𝟙` because
`i.f n ≫ w n = 0`.

The last section instantiates this with `p = Work.Cohomology.smallProj` and the contraction
`κ` of `Work.Cohomology.existsSmallChainsContraction` (whose acyclicity input is
`Work.Cohomology.exists_sub_small_of_boundary_small`), giving the strict retraction
`smallToSingRetraction`.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

set_option linter.style.haveILetI false

namespace Work.Serre.MVGlue

noncomputable section

/-- **A degreewise split mono of chain complexes whose complement is contracted is a split mono.**

`i : A ⟶ B` is a chain map, `p` a degreewise retraction of `i`, and `κ` contracts the complement
of the image of `i` (the hypotheses `h1`, `h2`, `h3` are exactly the shape in which
`Work.Cohomology.existsSmallChainsContraction` produces this data).  Then there is a chain map
`v : B ⟶ A` with `i ≫ v = 𝟙`.

The retraction is explicit: `v n = p n - κ n ≫ B.d (n+1) n ≫ p n`. -/
theorem exists_retraction_of_contraction {A B : ChainComplex (ModuleCat ℤ) ℕ} (i : A ⟶ B)
    (p : ∀ n, B.X n ⟶ A.X n) (hp : ∀ n, i.f n ≫ p n = 𝟙 (A.X n))
    (κ : ∀ n, B.X n ⟶ B.X (n + 1))
    (h1 : ∀ n, (p n ≫ i.f n) ≫ κ n = 0)
    (h2 : ∀ n, κ n ≫ (p (n + 1) ≫ i.f (n + 1)) = 0)
    (h3 : ∀ n, (κ (n + 1) ≫ B.d (n + 2) (n + 1) + B.d (n + 1) n ≫ κ n - 𝟙 (B.X (n + 1))) ≫
      (𝟙 (B.X (n + 1)) - p (n + 1) ≫ i.f (n + 1)) = 0) :
    ∃ v : B ⟶ A, i ≫ v = 𝟙 A := by
  -- `i` is degreewise injective, being a degreewise split mono
  have hinj : ∀ n, Function.Injective (i.f n).hom := by
    intro n x y hxy
    have hx := congrArg (fun (g : A.X n ⟶ A.X n) => (g : A.X n → A.X n) x) (hp n)
    have hy := congrArg (fun (g : A.X n ⟶ A.X n) => (g : A.X n → A.X n) y) (hp n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
      LinearMap.id_apply] at hx hy
    rw [hxy] at hx
    exact hx.symm.trans hy
  have hmono : ∀ n, Mono (i.f n) := fun n => (ModuleCat.mono_iff_injective _).mpr (hinj n)
  -- `i` kills `κ`
  have hiκ : ∀ n, i.f n ≫ κ n = 0 := by
    intro n
    calc i.f n ≫ κ n = (i.f n ≫ p n) ≫ i.f n ≫ κ n := by rw [hp n, Category.id_comp]
      _ = i.f n ≫ ((p n ≫ i.f n) ≫ κ n) := by simp only [Category.assoc]
      _ = 0 := by rw [h1 n, Limits.comp_zero]
  -- `κ` kills `p`
  have hκp : ∀ n, κ n ≫ p (n + 1) = 0 := by
    intro n
    haveI := hmono (n + 1)
    rw [← cancel_mono (i.f (n + 1))]
    rw [Category.assoc, h2 n, Limits.zero_comp]
  -- the defect of `p` being a chain map
  have hiΛ : ∀ m, i.f (m + 1) ≫
      (p (m + 1) ≫ A.d (m + 1) m - B.d (m + 1) m ≫ p m) = 0 := by
    intro m
    rw [Preadditive.comp_sub]
    have h1' : i.f (m + 1) ≫ (p (m + 1) ≫ A.d (m + 1) m) = A.d (m + 1) m := by
      rw [← Category.assoc, hp (m + 1), Category.id_comp]
    have h2' : i.f (m + 1) ≫ (B.d (m + 1) m ≫ p m) = A.d (m + 1) m := by
      rw [← Category.assoc, HomologicalComplex.Hom.comm i (m + 1) m, Category.assoc, hp m,
        Category.comp_id]
    rw [h1', h2', sub_self]
  -- the key computation: `w (n+1) ≫ d - d ≫ w n = Λ (n+1)`
  have key : ∀ n : ℕ,
      (κ (n + 1) ≫ B.d (n + 2) (n + 1) ≫ p (n + 1)) ≫ A.d (n + 1) n
        - B.d (n + 1) n ≫ (κ n ≫ B.d (n + 1) n ≫ p n)
      = p (n + 1) ≫ A.d (n + 1) n - B.d (n + 1) n ≫ p n := by
    intro n
    set Λ := p (n + 1) ≫ A.d (n + 1) n - B.d (n + 1) n ≫ p n with hΛdef
    set E := κ (n + 1) ≫ B.d (n + 2) (n + 1) + B.d (n + 1) n ≫ κ n - 𝟙 (B.X (n + 1)) with hEdef
    -- `θ ≫ Λ = 0`
    have hθΛ : (p (n + 1) ≫ i.f (n + 1)) ≫ Λ = 0 := by
      rw [hΛdef, Category.assoc, hiΛ n, Limits.comp_zero]
    -- `E ≫ θ = E`
    have hEeq : E = E ≫ (p (n + 1) ≫ i.f (n + 1)) := by
      have h3n : E ≫ (𝟙 (B.X (n + 1)) - p (n + 1) ≫ i.f (n + 1)) = 0 := by
        rw [hEdef]
        exact h3 n
      have hsum : (𝟙 (B.X (n + 1)) - p (n + 1) ≫ i.f (n + 1)) + (p (n + 1) ≫ i.f (n + 1))
          = 𝟙 (B.X (n + 1)) := sub_add_cancel _ _
      calc E = E ≫ 𝟙 (B.X (n + 1)) := (Category.comp_id E).symm
        _ = E ≫ ((𝟙 (B.X (n + 1)) - p (n + 1) ≫ i.f (n + 1))
              + (p (n + 1) ≫ i.f (n + 1))) := by rw [hsum]
        _ = E ≫ (𝟙 (B.X (n + 1)) - p (n + 1) ≫ i.f (n + 1))
              + E ≫ (p (n + 1) ≫ i.f (n + 1)) := Preadditive.comp_add _ _ _ _ _ _
        _ = E ≫ (p (n + 1) ≫ i.f (n + 1)) := by rw [h3n, zero_add]
    have hEΛ : E ≫ Λ = 0 := by
      rw [hEeq, Category.assoc, hθΛ, Limits.comp_zero]
    -- the expanded form of `E ≫ Λ = 0`
    have hmain : κ (n + 1) ≫ B.d (n + 2) (n + 1) ≫ Λ = Λ - B.d (n + 1) n ≫ κ n ≫ Λ := by
      have h := hEΛ
      rw [hEdef, Preadditive.sub_comp, Preadditive.add_comp, Category.id_comp] at h
      simp only [Category.assoc] at h
      rw [eq_sub_iff_add_eq]
      exact sub_eq_zero.mp h
    -- `p (n+1) ≫ d = Λ + B.d ≫ p n`
    have hpΛ : p (n + 1) ≫ A.d (n + 1) n = Λ + B.d (n + 1) n ≫ p n := by
      rw [hΛdef]; abel
    -- the first part of the correction
    have hA : (κ (n + 1) ≫ B.d (n + 2) (n + 1) ≫ p (n + 1)) ≫ A.d (n + 1) n
        = κ (n + 1) ≫ B.d (n + 2) (n + 1) ≫ Λ := by
      simp only [Category.assoc]
      rw [hpΛ, Preadditive.comp_add, Preadditive.comp_add]
      rw [show B.d (n + 2) (n + 1) ≫ (B.d (n + 1) n ≫ p n) = 0 from by
        rw [← Category.assoc, HomologicalComplex.d_comp_d, Limits.zero_comp]]
      simp
    -- the second part of the correction
    have hcomb : Λ - B.d (n + 1) n ≫ κ n ≫ Λ
          - B.d (n + 1) n ≫ (κ n ≫ B.d (n + 1) n ≫ p n)
        = Λ - B.d (n + 1) n ≫ κ n ≫ (p (n + 1) ≫ A.d (n + 1) n) := by
      rw [hpΛ]
      simp only [Preadditive.comp_add]
      abel
    have hzp : B.d (n + 1) n ≫ κ n ≫ p (n + 1) ≫ A.d (n + 1) n = 0 := by
      rw [show B.d (n + 1) n ≫ κ n ≫ p (n + 1) ≫ A.d (n + 1) n
          = (B.d (n + 1) n ≫ (κ n ≫ p (n + 1))) ≫ A.d (n + 1) n from by
        simp only [Category.assoc]]
      rw [hκp n, Limits.comp_zero, Limits.zero_comp]
    rw [hA, hmain, hcomb, hzp, sub_zero]
  refine ⟨{ f := fun m => p m - κ m ≫ B.d (m + 1) m ≫ p m
            comm' := ?_ }, ?_⟩
  · intro m q hmq
    rw [← hmq]
    rw [← sub_eq_zero]
    rw [Preadditive.sub_comp, Preadditive.comp_sub]
    have h1' : (p (q + 1) ≫ A.d (q + 1) q
            - (κ (q + 1) ≫ B.d (q + 2) (q + 1) ≫ p (q + 1)) ≫ A.d (q + 1) q)
          - (B.d (q + 1) q ≫ p q - B.d (q + 1) q ≫ (κ q ≫ B.d (q + 1) q ≫ p q))
        = (p (q + 1) ≫ A.d (q + 1) q - B.d (q + 1) q ≫ p q)
          - ((κ (q + 1) ≫ B.d (q + 2) (q + 1) ≫ p (q + 1)) ≫ A.d (q + 1) q
              - B.d (q + 1) q ≫ (κ q ≫ B.d (q + 1) q ≫ p q)) := by abel
    rw [h1', key q, sub_self]
  · rw [HomologicalComplex.Hom.ext_iff]
    funext m
    rw [HomologicalComplex.comp_f, HomologicalComplex.id_f]
    show i.f m ≫ (p m - κ m ≫ B.d (m + 1) m ≫ p m) = 𝟙 (A.X m)
    rw [Preadditive.comp_sub, hp m]
    have hz : i.f m ≫ (κ m ≫ B.d (m + 1) m ≫ p m) = 0 := by
      rw [← Category.assoc, hiκ m, Limits.zero_comp]
    rw [hz, sub_zero]

end

/-! ## The strict retraction of the small chains -/

/-- **The inclusion of the small chains admits a strict chain-level retraction.**

For an open cover `X = U ∪ V`, the inclusion `smallToSing U V` of the small chains into the
singular chains of `X` is a split monomorphism of chain complexes. -/
theorem smallToSingRetraction (X : TopCat) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) :
    ∃ v : Work.Cohomology.singularChains ℤ X ⟶ Work.Cohomology.smallChains U V,
      CategoryTheory.CategoryStruct.comp (Work.Cohomology.smallToSing U V) v
        = CategoryTheory.CategoryStruct.id (Work.Cohomology.smallChains U V) := by
  obtain ⟨hcomp, hgenS, hgenN⟩ := Work.Cohomology.smallProj_spec (X := X) U V
  have hr2 : ∀ n (σ : Work.Cohomology.Simplex X n) (h : Work.Cohomology.IsSmall U V σ),
      ((Work.Cohomology.smallToSing U V).f n)
          ((Work.Cohomology.smallProj U V n) (Work.Cohomology.gen X n σ))
        = Work.Cohomology.gen X n σ := by
    intro n σ h
    rw [hgenS n σ h]
    exact Work.Cohomology.smallToSing_gen ⟨σ, h⟩
  obtain ⟨κ, h1, h2, _h3zero, h3⟩ :=
    Work.Cohomology.existsSmallChainsContraction U V (Work.Cohomology.smallProj U V) hcomp hr2
      hgenN (Work.Cohomology.exists_sub_small_of_boundary_small U V hU hV hcov)
  exact exists_retraction_of_contraction (Work.Cohomology.smallToSing U V)
    (Work.Cohomology.smallProj U V) hcomp κ h1 h2 h3

end Work.Serre.MVGlue
