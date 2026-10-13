import Mathlib
import Submission.Work.DSMX0U.ModelF

/-!
# DSMX0U — the tower model is a bounded-above complex of finitely generated free modules

The model complex of the tower,

  `towerModel hstep M s₀ = (towerComplex hstep M s₀).extend (embeddingUpIntLE M)`,

places the level `k` of the tower in the cohomological degree `levelDeg M k - 1 = M - k` and is
zero above `M`.  The term of the model in the degree of a level is `(tower k).G`, which is the
product `pairMod A gen rel` of the two finitely generated free modules of the cell
(`Cell.freeGen`, `Cell.finiteGen`, `Cell.freeRel`, `Cell.finiteRel`).  Hence every term of the
model is a finitely generated free `A`-module and the model vanishes above `M`, which is exactly
`DSMap.Mix.IsBddFinFree`.

The two ingredients are `Work.DSMX0U.towerModel_isZero_of_gt` (boundedness) and
`Work.DSMX0U.towerModelXIso` (the identification of a term of the model with the term of a level
of the tower); the only remaining work is transporting finiteness and freeness along that
isomorphism.
-/

set_option linter.style.haveILetI false

namespace Work.DSMX0U

universe a

open CategoryTheory Limits

variable {A : Type a} [CommRing A]
variable {C : CochainComplex (ModuleCat.{a} A) ℤ} {c₀ : ModuleCat.of A A ⟶ C.X 0}

/-- The term of a level of the tower is a free `A`-module: it is the product of the module of
generators and the module of relations of the cell, both of which are free. -/
theorem tower_G_free (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ) : Module.Free A ↥((tower hstep M s₀ k).G A) := by
  haveI := (tower hstep M s₀ k).freeGen
  haveI := (tower hstep M s₀ k).freeRel
  infer_instance

/-- The term of a level of the tower is a finitely generated `A`-module: it is the product of the
module of generators and the module of relations of the cell, both of which are finitely
generated. -/
theorem tower_G_finite (hstep : ∀ (q : ℤ) (s : Cell A C c₀ q), StepData A s) (M : ℤ)
    (s₀ : Cell A C c₀ (M + 1)) (k : ℕ) : Module.Finite A ↥((tower hstep M s₀ k).G A) := by
  haveI := (tower hstep M s₀ k).finiteGen
  haveI := (tower hstep M s₀ k).finiteRel
  infer_instance

/-- **The model of the tower is a bounded-above complex of finitely generated free modules.**

In a degree `i ≤ M` there is a level `k` with `levelDeg M k - 1 = i`, and `towerModelXIso`
identifies `(towerModel hstep M s₀).X i` with `(tower k).G`, a product of finitely generated free
modules; in a degree `i > M` the model is zero (`towerModel_isZero_of_gt`), hence a subsingleton,
hence free and finitely generated.  The boundedness bound is `M`. -/
theorem isBddFinFree_towerModel {A : Type a} [CommRing A]
    {C : CochainComplex (ModuleCat.{a} A) ℤ} {c₀ : ModuleCat.of A A ⟶ C.X 0}
    (hstep : ∀ (q : ℤ) (s : Work.DSMX0U.Cell A C c₀ q), Work.DSMX0U.StepData A s)
    (M : ℤ) (s₀ : Work.DSMX0U.Cell A C c₀ (M + 1)) :
    DSMap.Mix.IsBddFinFree (Work.DSMX0U.towerModel hstep M s₀) := by
  refine ⟨fun i => ?_, M, fun i hi => towerModel_isZero_of_gt hstep M s₀ hi⟩
  by_cases h : ∃ k : ℕ, levelDeg M k - 1 = i
  · obtain ⟨k, hk⟩ := h
    have hfree : Module.Free A ↥((tower hstep M s₀ k).G A) := tower_G_free hstep M s₀ k
    have hfin : Module.Finite A ↥((tower hstep M s₀ k).G A) := tower_G_finite hstep M s₀ k
    have e : (towerModel hstep M s₀).X i ≅ (tower hstep M s₀ k).G A :=
      (HomologicalComplex.XIsoOfEq (towerModel hstep M s₀) hk.symm) ≪≫
        (towerModelXIso hstep M s₀ k)
    exact ⟨Module.Free.of_equiv e.symm.toLinearEquiv,
      Module.Finite.equiv e.symm.toLinearEquiv⟩
  · have hgt : M < i := gt_of_not_exists_levelOf M i h
    haveI : Subsingleton ↥((towerModel hstep M s₀).X i) :=
      ModuleCat.subsingleton_of_isZero (towerModel_isZero_of_gt hstep M s₀ hgt)
    exact ⟨inferInstance, inferInstance⟩

end Work.DSMX0U
