import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.RatHurewicz.cycleModelDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RatHurewicz

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial
open scoped Topology Simplicial unitInterval

attribute [local implicit_reducible] AlgebraicTopology.singularChainComplexFunctor

open Classical

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X}

/-! ## Auxiliary lemmas -/

/-- The generator attached to a simplex, in the `Simp` presentation. -/
theorem genQ_symm {Y : Type} [TopologicalSpace Y] (n : ℕ)
    (x : (TopCat.toSSet.obj (TopCat.of Y)) _⦋n⦌) :
    genQ (Y := Y) n ((TopCat.toSSetObjEquivT (TopCat.of Y) (Opposite.op (SimplexCategory.mk n))) x)
      = Work.Cohomology.genElt ℚ (TopCat.toSSet.obj (TopCat.of Y)) x := by
  show Work.Cohomology.genElt ℚ (TopCat.toSSet.obj (TopCat.of Y))
      ((TopCat.toSSetObjEquivT (TopCat.of Y) (Opposite.op (SimplexCategory.mk n))).symm
        ((TopCat.toSSetObjEquivT (TopCat.of Y) (Opposite.op (SimplexCategory.mk n))) x))
    = Work.Cohomology.genElt ℚ (TopCat.toSSet.obj (TopCat.of Y)) x
  rw [Equiv.symm_apply_apply]

/-- `coordsQ`-coordinates of the generator attached to a simplex. -/
theorem coordsQ_genQ {Y : Type} [TopologicalSpace Y] (n : ℕ)
    (s : Work.EmbeddedSpheres.Hurewicz.Simp (TopCat.of Y) n) :
    Work.StemsB.coordsQ (TopCat.toSSet.obj (TopCat.of Y)) n (genQ (Y := Y) n s)
      = Finsupp.single
          ((TopCat.toSSetObjEquivT (TopCat.of Y) (Opposite.op (SimplexCategory.mk n))).symm s)
          (1 : ℚ) := by
  show Work.StemsB.coordsQ (TopCat.toSSet.obj (TopCat.of Y)) n
      (Work.Cohomology.genElt ℚ (TopCat.toSSet.obj (TopCat.of Y))
        ((TopCat.toSSetObjEquivT (TopCat.of Y) (Opposite.op (SimplexCategory.mk n))).symm s))
    = Finsupp.single _ (1 : ℚ)
  rw [Work.Cohomology.genElt, Work.StemsB.coordsQ_ι]

/-- A chain whose `coordsQ`-coordinates vanish is zero. -/
theorem eq_zero_of_coordsQ_eq_zero {A : SSet} {n : ℕ}
    {u : (A.chainComplex (ModuleCat.of ℚ ℚ)).X n}
    (h : Work.StemsB.coordsQ A n u = 0) : u = 0 := by
  have h1 := LinearMap.congr_fun (Work.StemsB.mkQ_comp_coordsQ A n) u
  rw [LinearMap.comp_apply, LinearMap.id_coe, id_eq] at h1
  rw [h, map_zero] at h1
  exact h1.symm

/-- The `p`-th face of a simplex is the composition with the face inclusion. -/
theorem face_eq_comp {Y : TopCat.{0}} {n : ℕ} (p : Fin (n + 2))
    (s : Work.EmbeddedSpheres.Hurewicz.Simp Y (n + 1)) :
    Work.EmbeddedSpheres.Hurewicz.face p s = s.comp (facept (n + 1) p) := rfl

/-- **The fibrewise regrouping lemma.**  If a formal sum of generators has zero fibres along a map
`τ`, and `sg` is constant on the fibres of `τ`, then the same sum with `sg` in place of `τ` is
zero. -/
theorem sum_smul_single_eq_zero_of_fiber {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (b : α → ℚ) (τ : α → β) (sg : α → γ)
    (hfib : ∀ a ∈ s, ∀ a' ∈ s, τ a = τ a' → sg a = sg a')
    (hzero : ∑ a ∈ s, b a • (Finsupp.single (τ a) (1 : ℚ) : β →₀ ℚ) = 0) :
    ∑ a ∈ s, b a • (Finsupp.single (sg a) (1 : ℚ) : γ →₀ ℚ) = 0 := by
  classical
  have hP : ∀ y : β, (∑ a ∈ s.filter (fun a => τ a = y), b a) = 0 := by
    intro y
    have h1 : (∑ a ∈ s.filter (fun a => τ a = y), b a)
        = (∑ a ∈ s, b a • (Finsupp.single (τ a) (1 : ℚ) : β →₀ ℚ)) y := by
      rw [Finsupp.finsetSum_apply, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
      by_cases h : τ a = y
      · rw [if_pos h, if_pos h, mul_one]
      · rw [if_neg h, if_neg h, mul_zero]
    rw [h1, hzero, Finsupp.zero_apply]
  have hmem : ∀ a ∈ s, τ a ∈ s.image τ := fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image τ) (g := τ) hmem
      (fun a => b a • (Finsupp.single (sg a) (1 : ℚ) : γ →₀ ℚ))]
  refine Finset.sum_eq_zero (fun y hy => ?_)
  obtain ⟨a₀, ha₀s, ha₀⟩ := Finset.mem_image.mp hy
  have hstep : (∑ a ∈ s.filter (fun a => τ a = y),
        b a • (Finsupp.single (sg a) (1 : ℚ) : γ →₀ ℚ))
      = (∑ a ∈ s.filter (fun a => τ a = y), b a) •
          (Finsupp.single (sg a₀) (1 : ℚ) : γ →₀ ℚ) := by
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [Finset.mem_filter] at ha
    rw [hfib a ha.1 a₀ ha₀s (by rw [ha.2, ha₀])]
  rw [hstep, hP y, zero_smul]

/-- The model chain of a cycle is a cycle: the boundary of `cycleChain` vanishes. The intended proof is the regrouping of `Work.RatHurewicz.cycleChain_d_expand` (already proved in `Submission.Work.RatHurewicz.cycleModelDefs`): expand `∂ (cycleChain)` as a sum over the pairs `(i, p)` of a top cell of the support and a face index, rewrite the summands via the key face relation `Work.RatHurewicz.face_topMap_eq` (two face maps into the model agree whenever the corresponding face maps to `X` agree), group the terms by the value of the `X`-simplex `face p (simplexMap i)` using `Finset.sum_fiberwise_of_maps_to`, identify each group's coefficient with the coefficient of that simplex in `∂ z` (expand `∂ z` with `Work.StemsB.chain_eq_sum_genQ` and `d_genQ` and take coordinates with `Work.StemsB.coordsQ`, using `coordsQ_ι`), and conclude with `hz : ∂ z = 0`. -/
theorem cycleChain_d {X : Type} [TopologicalSpace X] {x₀ : X}
    (hconnX : Subsingleton (HomotopyGroup (Fin 0) X x₀)) (n : ℕ)
    (z : (Work.Cohomology.singularChains ℚ (TopCat.of X)).X (n + 1))
    (hz : (Work.Cohomology.singularChains ℚ (TopCat.of X)).d (n + 1) n z = 0) :
    (Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.RatHurewicz.cycleModelSpace hconnX n z))).d (n + 1) n
      (Work.RatHurewicz.cycleChain hconnX n z) = 0 := by
  classical
  -- (A) the coordinates of the boundary of the model chain
  have hA : Work.StemsB.coordsQ
        (TopCat.toSSet.obj (TopCat.of (cycleModelSpace hconnX n z))) n
        ((Work.Cohomology.singularChains ℚ
          (TopCat.of (cycleModelSpace hconnX n z))).d (n + 1) n (cycleChain hconnX n z))
      = ∑ ip ∈ (cycleSupport (n + 1) z).attach.product (Finset.univ : Finset (Fin (n + 2))),
          (cycleCoeff (n + 1) z ip.1.1 * ((-1 : ℚ) ^ (ip.2 : ℕ))) •
            Finsupp.single ((TopCat.toSSetObjEquivT
                (TopCat.of (cycleModelSpace hconnX n z))
                (Opposite.op (SimplexCategory.mk n))).symm
              (Work.EmbeddedSpheres.Hurewicz.face ip.2
                (topMap (cycleMData hconnX n z) ip.1))) (1 : ℚ) := by
    rw [cycleChain_d_expand hconnX n z, map_sum]
    refine Finset.sum_congr rfl (fun ip _ => ?_)
    rw [map_smul, coordsQ_genQ]
  -- the expansion of `z` as a sum of generators
  have hzsum : z = ∑ i ∈ (cycleSupport (n + 1) z).attach,
      cycleCoeff (n + 1) z i.1 •
        genQ (Y := X) (n + 1) ((TopCat.toSSetObjEquivT (TopCat.of X)
          (Opposite.op (SimplexCategory.mk (n + 1)))) i.1) := by
    conv_lhs =>
      rw [Work.StemsB.chain_eq_sum_genQ (TopCat.toSSet.obj (TopCat.of X)) (n + 1) z]
    rw [show (Work.StemsB.coordsQ (TopCat.toSSet.obj (TopCat.of X)) (n + 1) z).support
        = cycleSupport (n + 1) z from rfl]
    rw [← Finset.sum_attach (cycleSupport (n + 1) z)
      (fun x => (Work.StemsB.coordsQ (TopCat.toSSet.obj (TopCat.of X)) (n + 1) z x) •
        (ModuleCat.Hom.hom ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
          (R := ModuleCat.of ℚ ℚ) x)) 1)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [cycleCoeff, genQ, Work.Cohomology.genElt, Equiv.symm_apply_apply]
  -- the expansion of the boundary of `z`
  have hzflat : (Work.Cohomology.singularChains ℚ (TopCat.of X)).d (n + 1) n z
      = ∑ ip ∈ (cycleSupport (n + 1) z).attach.product (Finset.univ : Finset (Fin (n + 2))),
          (cycleCoeff (n + 1) z ip.1.1 * ((-1 : ℚ) ^ (ip.2 : ℕ))) •
            genQ (Y := X) n (Work.EmbeddedSpheres.Hurewicz.face ip.2
              ((cycleMData hconnX n z).simplexMap ip.1)) := by
    conv_lhs => rw [hzsum]
    rw [map_sum]
    have hprod : (∑ ip ∈ (cycleSupport (n + 1) z).attach.product
          (Finset.univ : Finset (Fin (n + 2))),
          (cycleCoeff (n + 1) z ip.1.1 * ((-1 : ℚ) ^ (ip.2 : ℕ))) •
            genQ (Y := X) n (Work.EmbeddedSpheres.Hurewicz.face ip.2
              ((cycleMData hconnX n z).simplexMap ip.1)))
        = ∑ i ∈ (cycleSupport (n + 1) z).attach,
            ∑ p ∈ (Finset.univ : Finset (Fin (n + 2))),
              (cycleCoeff (n + 1) z i.1 * ((-1 : ℚ) ^ (p : ℕ))) •
                genQ (Y := X) n (Work.EmbeddedSpheres.Hurewicz.face p
                  ((cycleMData hconnX n z).simplexMap i)) :=
      Finset.sum_product _ _ _
    rw [hprod]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, d_genQ (Y := X) n ((TopCat.toSSetObjEquivT (TopCat.of X)
      (Opposite.op (SimplexCategory.mk (n + 1)))) i.1), Finset.smul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [smul_smul]
    rfl
  -- (B) the coordinates of the boundary of `z` vanish
  have hB : Work.StemsB.coordsQ (TopCat.toSSet.obj (TopCat.of X)) n
      ((Work.Cohomology.singularChains ℚ (TopCat.of X)).d (n + 1) n z)
      = ∑ ip ∈ (cycleSupport (n + 1) z).attach.product (Finset.univ : Finset (Fin (n + 2))),
          (cycleCoeff (n + 1) z ip.1.1 * ((-1 : ℚ) ^ (ip.2 : ℕ))) •
            Finsupp.single ((TopCat.toSSetObjEquivT (TopCat.of X)
                (Opposite.op (SimplexCategory.mk n))).symm
              (Work.EmbeddedSpheres.Hurewicz.face ip.2
                ((cycleMData hconnX n z).simplexMap ip.1))) (1 : ℚ) := by
    rw [hzflat, map_sum]
    refine Finset.sum_congr rfl (fun ip _ => ?_)
    rw [map_smul, coordsQ_genQ]
  have hB0 : (∑ ip ∈ (cycleSupport (n + 1) z).attach.product
        (Finset.univ : Finset (Fin (n + 2))),
        (cycleCoeff (n + 1) z ip.1.1 * ((-1 : ℚ) ^ (ip.2 : ℕ))) •
          Finsupp.single ((TopCat.toSSetObjEquivT (TopCat.of X)
              (Opposite.op (SimplexCategory.mk n))).symm
            (Work.EmbeddedSpheres.Hurewicz.face ip.2
              ((cycleMData hconnX n z).simplexMap ip.1))) (1 : ℚ)) = 0 := by
    rw [← hB, hz, map_zero]
  -- the same sum, with the `n`-simplices of the model in place of those of `X`
  have hkey : (∑ ip ∈ (cycleSupport (n + 1) z).attach.product
        (Finset.univ : Finset (Fin (n + 2))),
        (cycleCoeff (n + 1) z ip.1.1 * ((-1 : ℚ) ^ (ip.2 : ℕ))) •
          Finsupp.single ((TopCat.toSSetObjEquivT
              (TopCat.of (cycleModelSpace hconnX n z))
              (Opposite.op (SimplexCategory.mk n))).symm
            (Work.EmbeddedSpheres.Hurewicz.face ip.2
              (topMap (cycleMData hconnX n z) ip.1))) (1 : ℚ)) = 0 := by
    refine sum_smul_single_eq_zero_of_fiber
      (s := (cycleSupport (n + 1) z).attach.product (Finset.univ : Finset (Fin (n + 2))))
      (b := fun ip => cycleCoeff (n + 1) z ip.1.1 * ((-1 : ℚ) ^ (ip.2 : ℕ)))
      (τ := fun ip => (TopCat.toSSetObjEquivT (TopCat.of X)
          (Opposite.op (SimplexCategory.mk n))).symm
        (Work.EmbeddedSpheres.Hurewicz.face ip.2
          ((cycleMData hconnX n z).simplexMap ip.1)))
      (sg := fun ip => (TopCat.toSSetObjEquivT (TopCat.of (cycleModelSpace hconnX n z))
          (Opposite.op (SimplexCategory.mk n))).symm
        (Work.EmbeddedSpheres.Hurewicz.face ip.2
          (topMap (cycleMData hconnX n z) ip.1)))
      ?_ hB0
    intro ip _ ip' _ h
    have h1 : Work.EmbeddedSpheres.Hurewicz.face ip.2
          ((cycleMData hconnX n z).simplexMap ip.1)
        = Work.EmbeddedSpheres.Hurewicz.face ip'.2
          ((cycleMData hconnX n z).simplexMap ip'.1) :=
      Equiv.injective _ h
    have h2 : ((cycleMData hconnX n z).simplexMap ip.1).comp (facept (n + 1) ip.2)
        = ((cycleMData hconnX n z).simplexMap ip'.1).comp (facept (n + 1) ip'.2) := by
      rw [← face_eq_comp (Y := TopCat.of X) ip.2 ((cycleMData hconnX n z).simplexMap ip.1),
        ← face_eq_comp (Y := TopCat.of X) ip'.2 ((cycleMData hconnX n z).simplexMap ip'.1)]
      exact h1
    have h3 : Work.EmbeddedSpheres.Hurewicz.face
          (X := TopCat.of (cycleModelSpace hconnX n z)) ip.2
          (topMap (cycleMData hconnX n z) ip.1)
        = Work.EmbeddedSpheres.Hurewicz.face
          (X := TopCat.of (cycleModelSpace hconnX n z)) ip'.2
          (topMap (cycleMData hconnX n z) ip'.1) := by
      show (topMap (cycleMData hconnX n z) ip.1).comp (facept (n + 1) ip.2)
          = (topMap (cycleMData hconnX n z) ip'.1).comp (facept (n + 1) ip'.2)
      exact face_topMap_eq (cycleMData hconnX n z) h2
    rw [h3]
  have hAN : Work.StemsB.coordsQ
        (TopCat.toSSet.obj (TopCat.of (cycleModelSpace hconnX n z))) n
        ((Work.Cohomology.singularChains ℚ
          (TopCat.of (cycleModelSpace hconnX n z))).d (n + 1) n (cycleChain hconnX n z)) = 0 := by
    rw [hA, hkey]
  exact eq_zero_of_coordsQ_eq_zero
    (A := TopCat.toSSet.obj (TopCat.of (cycleModelSpace hconnX n z))) (n := n) hAN

end

end Work.RatHurewicz
