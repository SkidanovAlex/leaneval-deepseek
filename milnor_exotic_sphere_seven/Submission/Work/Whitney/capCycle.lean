import Mathlib
import Submission.Work.Whitney.lowerCap
import Submission.Work.Cohomology.PushChain
import Submission.Work.Cohomology.SmallChains
import Submission.Work.Whitney.sdIter_smallChain_local
import Submission.Work.Whitney.CupDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The cap cycle `capX_* B − lcapX_* B`

The first geometric ingredient of Route A (`rankOne_cup_model_NOTES.md` §42i item 1): for a chain `B`
of `Y × MBall n` whose boundary is carried by `DiscB Y n`, the difference of the push-forwards of `B`
along the **upper** cap `capX` (`rankOne_cup_model.lean`) and the **lower** cap `lowerCapX`
(`lowerCap.lean`) is a **cycle** on the sphere — because the two caps agree on `DiscB`
(`lowerCapMap_eq_capMap_of_mem_mSph`), so their push-forwards agree on the boundary.

This file proves the point-level agreement and the generator-level chain agreement; the passage to
arbitrary `DiscB`-small chains is the `Submodule.comap` + `mem_of_genSSet` pattern already used in
`exists_iter_small_chain_of_smallSupport` and `kronecker_eq_zero_of_isSmallChain_of_mem_relKern`.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Whitney

open Work.Thom
open Work.Cohomology

noncomputable section

/-- **The two caps agree on the sphere part.**  `capX` and `lowerCapX` are the two graphs over the
ball; on `DiscB Y n` (the fibre sphere) they coincide, because both have last coordinate
`√(1-‖u‖²) = 0` there. -/
theorem capX_eq_lowerCapX_of_mem_discB (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (q : Y × MBall n) (hq : q.2.1 ∈ mSph n) : capX Y n q = lowerCapX Y n q := by
  refine Prod.ext rfl ?_
  rw [capX_apply, lowerCapX_apply, lowerCapMap_eq_capMap_of_mem_mSph n hq]

/-- **The push-forwards of a generator supported on `DiscB` agree**, for the two caps. -/
theorem pushChain_capX_gen_eq_of_mem_discB (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (σ : Simplex (TopCat.of (Y × MBall n)) n)
    (hσ : ∀ z, (TopCat.toSSetObjEquivOld (TopCat.of (Y × MBall n)) (Opposite.op ⦋n⦌) σ z).2.1
      ∈ mSph n) :
    pushChain (TopCat.of (Y × MBall n)) (TopCat.of (tcmX Y n 1)) (TopCat.ofHom (capX Y n)) n
        (gen (TopCat.of (Y × MBall n)) n σ)
      = pushChain (TopCat.of (Y × MBall n)) (TopCat.of (tcmX Y n 1))
          (TopCat.ofHom (lowerCapX Y n)) n (gen (TopCat.of (Y × MBall n)) n σ) := by
  rw [pushChain_gen, pushChain_gen]
  congr 1
  apply (TopCat.toSSetObjEquivOld (TopCat.of (tcmX Y n 1)) (Opposite.op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro z
  rw [TopCat.toSSetObjEquivOld_map_apply, TopCat.toSSetObjEquivOld_map_apply]
  exact capX_eq_lowerCapX_of_mem_discB Y n _ (hσ z)

/-- **Push-forwards of a generator supported in `S` agree** for two maps agreeing on `S`. -/
theorem pushChain_gen_eq_of_isSmall {X Z : TopCat} (f g : X ⟶ Z) {S : Set X}
    (hS : ∀ x, x ∈ S → f x = g x) {n : ℕ} {σ : Simplex X n} (hσ : IsSmall S (∅ : Set X) σ) :
    pushChain X Z f n (gen X n σ) = pushChain X Z g n (gen X n σ) := by
  rw [pushChain_gen, pushChain_gen]
  congr 1
  apply (TopCat.toSSetObjEquivOld Z (Opposite.op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro z
  rw [TopCat.toSSetObjEquivOld_map_apply, TopCat.toSSetObjEquivOld_map_apply]
  refine hS _ ?_
  rw [isSmall_iff] at hσ
  rcases hσ with h | h
  · exact h (Set.mem_range_self z)
  · exfalso
    rcases Set.range_nonempty (fun z : (Delta n : TopCat) => sdMap n σ z) with ⟨y, hy⟩
    simpa using h hy

/-- **Two push-forwards agree on a chain carried by the set where the two maps agree.** -/
theorem pushChain_eq_of_isSmallChain {X Z : TopCat} (f g : X ⟶ Z) (S : Set X)
    (hS : ∀ x, x ∈ S → f x = g x) (n : ℕ)
    (c : (singularChains ℤ X).X n) (hc : IsSmallChain S (∅ : Set X) c) :
    pushChain X Z f n c = pushChain X Z g n c := by
  classical
  obtain ⟨c', hc'⟩ := hc
  rw [← hc']
  let Φ : (↑((smallChains S (∅ : Set X)).X n)) →ₗ[ℤ] (↑((singularChains ℤ Z).X n)) :=
    ((pushChain X Z f n).comp ((smallToSing S (∅ : Set X)).f n).hom)
      - ((pushChain X Z g n).comp ((smallToSing S (∅ : Set X)).f n).hom)
  have hQ : LinearMap.ker Φ = ⊤ := by
    refine mem_of_genSSet (smallSSet S (∅ : Set X)) n (LinearMap.ker Φ) ?_
    intro τ
    show Φ (genSSet (smallSSet S (∅ : Set X)) n τ) = 0
    simp only [Φ, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply]
    rw [smallToSing_gen τ, pushChain_gen_eq_of_isSmall f g hS τ.2, sub_self]
  have hmem : c' ∈ LinearMap.ker Φ := by rw [hQ]; exact Submodule.mem_top
  have hzero : (pushChain X Z f n) ((smallToSing S (∅ : Set X)).f n |>.hom c')
      - (pushChain X Z g n) ((smallToSing S (∅ : Set X)).f n |>.hom c') = 0 := hmem
  exact sub_eq_zero.mp hzero

/-- **The cap cycle**: for a chain `B` of `Y × MBall n` whose boundary is carried by `DiscB Y n`, the
difference of the two cap push-forwards is a **cycle** — no primitive and no radial parametrisation,
just the agreement of the two caps on the sphere (`capX_eq_lowerCapX_of_mem_discB`). -/
theorem capX_sub_lowerCapX_cycle (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (B : (singularChains ℤ (TopCat.of (Y × MBall n))).X n)
    (hB : IsSmallChain (DiscB Y n) (∅ : Set (Y × MBall n))
      (((singularChains ℤ (TopCat.of (Y × MBall n))).d n (n - 1)) B)) :
    ((singularChains ℤ (TopCat.of (tcmX Y n 1))).d n (n - 1))
        (pushChain (TopCat.of (Y × MBall n)) (TopCat.of (tcmX Y n 1))
            (TopCat.ofHom (capX Y n)) n B
          - pushChain (TopCat.of (Y × MBall n)) (TopCat.of (tcmX Y n 1))
              (TopCat.ofHom (lowerCapX Y n)) n B) = 0 := by
  have hdX (f : TopCat.of (Y × MBall n) ⟶ TopCat.of (tcmX Y n 1)) :
      ((singularChains ℤ (TopCat.of (tcmX Y n 1))).d n (n - 1))
          (pushChain (TopCat.of (Y × MBall n)) (TopCat.of (tcmX Y n 1)) f n B)
        = pushChain (TopCat.of (Y × MBall n)) (TopCat.of (tcmX Y n 1)) f (n - 1)
            (((singularChains ℤ (TopCat.of (Y × MBall n))).d n (n - 1)) B) := by
    have h := congrArg (fun (g : (singularChains ℤ (TopCat.of (Y × MBall n))).X n ⟶
        (singularChains ℤ (TopCat.of (tcmX Y n 1))).X (n - 1)) => g.hom B)
      (HomologicalComplex.Hom.comm
        (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ)) n (n - 1))
    exact h
  have hagree := pushChain_eq_of_isSmallChain (TopCat.ofHom (capX Y n))
    (TopCat.ofHom (lowerCapX Y n)) (DiscB Y n)
    (fun q hq => capX_eq_lowerCapX_of_mem_discB Y n q hq) (n - 1)
    (((singularChains ℤ (TopCat.of (Y × MBall n))).d n (n - 1)) B) hB
  rw [map_sub, hdX (TopCat.ofHom (capX Y n)), hdX (TopCat.ofHom (lowerCapX Y n)), hagree,
    sub_self]

end


/-! ## The identity simplex of `Δᵖ`

`Work.Cohomology.linSimplex` with the vertices of the standard simplex; its underlying map is the
identity (`Work.Cohomology.affineSimplex_id`).  It is the source of the "fundamental chain" of the
disc pair, `pushChain f (gen (Δᵖ) p (idSimplex p))`, of `NOTES_tcmRankOneSusp.md` §20.5. -/

/-- The identity `p`-simplex of `Δᵖ`. -/
noncomputable def idSimplex (p : ℕ) : Work.Cohomology.Simplex (Work.Cohomology.Delta p) p :=
  Work.Cohomology.linSimplex (fun i : Fin (p+1) => stdSimplex.vertex i)

theorem sdMap_idSimplex (p : ℕ) (z : stdSimplex ℝ (Fin (p+1))) :
    Work.Cohomology.sdMap p (idSimplex p) z = z :=
  Work.Cohomology.affineSimplex_id z

end Work.Whitney

/-! ## Axiom check -/

#print axioms Work.Whitney.capX_eq_lowerCapX_of_mem_discB
#print axioms Work.Whitney.pushChain_eq_of_isSmallChain
#print axioms Work.Whitney.capX_sub_lowerCapX_cycle
