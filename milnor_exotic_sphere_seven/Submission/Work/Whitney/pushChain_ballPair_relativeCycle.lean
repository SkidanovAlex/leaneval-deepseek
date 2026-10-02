import Mathlib
import Submission.Work.Whitney.capCycle
import Submission.Work.Whitney.ballChain_boundary_isSmall
import Submission.Work.Cohomology.Sd_comm
import Submission.Work.Cohomology.Affine

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The pushed fundamental chain of the ball pair is a relative cycle

`Work.Whitney.exists_ballChain` (see `NOTES_tcmRankOneSusp.md` §20.5) needs a chain `B` of
`Y × MBall n` whose boundary is carried by the sphere part `DiscB Y n`.  The chain is the
push-forward of the fundamental chain of `Δⁿ` along a *map of pairs*
`f : (Δⁿ, ∂Δⁿ) → (Y × MBall n, DiscB Y n)`:

  `B = pushChain f (gen (idSimplex n))`,  `∂B ∈ C_*(DiscB Y n)`.

`Work.Whitney.ballChain_boundary_isSmall` proves the purely combinatorial half: if *every face* of
the pushed simplex lands in `DiscB`, then `∂B` is a small chain.  The present file supplies the
geometric input: the faces of the pushed identity simplex are precisely the restrictions of `f` to
the faces `faceMap m i (Δ^m)` of `Δ^{m+1}`, so the hypothesis "`f` maps `∂Δⁿ` into `DiscB`" — stated
here at the level of points, `∃ i, z i = 0 → f z ∈ DiscB`, which is what a construction of `f`
naturally provides — gives the face condition of `ballChain_boundary_isSmall`.

The two ingredients of the computation are

* `TopCat.toSSetObjEquivOld_δ_apply`: evaluating the `i`-th face of a pushed simplex at `z` is
  evaluating the simplex at the affine face point `stdSimplex.map i.succAbove z` (whose `i`-th
  coordinate is `0`, `faceMap_zero`);
* `TopCat.toSSetObjEquivOld_map_apply`: the pushed simplex is `f` composed with the simplex, and the identity
  simplex of `Δⁿ` is the identity (so `f` is evaluated exactly at the face point).
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Whitney

open Work.Cohomology
open Work.Thom

noncomputable section

/-- The identity simplex of `Δⁿ`, evaluated at a point, is that point. -/
lemma toSSetObjEquiv_idSimplex (p : ℕ) (z : stdSimplex ℝ (Fin (p+1))) :
    TopCat.toSSetObjEquivOld (Delta p) (Opposite.op ⦋p⦌) (idSimplex p) z = z :=
  sdMap_idSimplex p z

/-- The `i`-th coordinate of the `i`-th face point of a simplex vanishes: this is the pointwise form
of `f(∂Δⁿ) ⊆ DiscB`. -/
lemma faceMap_apply_eq_zero (m : ℕ) (i : Fin (m+2)) (z : stdSimplex ℝ (Fin (m+1))) :
    (((faceMap m i) z : stdSimplex ℝ (Fin (m+2))) : Fin (m+2) → ℝ) i = 0 := by
  show (((stdSimplex.map i.succAbove z) : stdSimplex ℝ (Fin (m+2))) : Fin (m+2) → ℝ) i = 0
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  exact Finset.sum_eq_zero (fun a ha => by
    rw [Finset.mem_filter] at ha
    exact absurd ha.2 (Fin.succAbove_ne i a))

/-- Pointwise form of smallness for the pair `(U, ∅)`. -/
theorem isSmall_empty_of_forall {X : TopCat} {U : Set X} {n : ℕ} {σ : Simplex X n}
    (h : ∀ z : stdSimplex ℝ (Fin (n+1)), TopCat.toSSetObjEquivOld X (Opposite.op ⦋n⦌) σ z ∈ U) :
    IsSmall U ∅ σ :=
  (isSmall_iff σ).mpr (Or.inl (Set.range_subset_iff.mpr h))

/-- **The face condition of the ball pair.**  If `f : Δ^{m+1} → Y × MBall (m+1)` maps the
`i`-th face of `Δ^{m+1}` into `DiscB Y (m+1)`, then the `i`-th face of the push-forward of the
identity simplex is a small simplex for `(DiscB Y (m+1), ∅)`. -/
theorem isSmall_delta_push_idSimplex (Y : Type) [TopologicalSpace Y] (m : ℕ)
    (f : Delta (m+1) ⟶ TopCat.of (Y × MBall (m+1)))
    (hbd : ∀ z : stdSimplex ℝ (Fin (m+2)),
      (∃ i : Fin (m+2), (z : Fin (m+2) → ℝ) i = 0) → f z ∈ DiscB Y (m+1))
    (i : Fin (m+2)) :
    IsSmall (DiscB Y (m+1)) ∅
      ((TopCat.toSSet.obj (TopCat.of (Y × MBall (m+1)))).δ i
        ((TopCat.toSSet.map f).app (Opposite.op ⦋m+1⦌) (idSimplex (m+1)))) := by
  refine isSmall_empty_of_forall (fun z => ?_)
  -- the face point: evaluate at the affine face point, then at `f`
  rw [TopCat.toSSetObjEquivOld_δ_apply, TopCat.toSSetObjEquivOld_map_apply, toSSetObjEquiv_idSimplex]
  exact hbd _ ⟨i, faceMap_apply_eq_zero m i z⟩

/-- **The pushed fundamental chain is a relative cycle**, in the `m + 1` form in which the
combinatorics of `ballChain_boundary_isSmall` is available. -/
theorem pushChain_ballPair_relativeCycle_aux (Y : Type) [TopologicalSpace Y] (m : ℕ)
    (f : Delta (m+1) ⟶ TopCat.of (Y × MBall (m+1)))
    (hbd : ∀ z : stdSimplex ℝ (Fin (m+2)),
      (∃ i : Fin (m+2), (z : Fin (m+2) → ℝ) i = 0) → f z ∈ DiscB Y (m+1)) :
    IsSmallChain (DiscB Y (m+1)) ∅
      ((singularChains ℤ (TopCat.of (Y × MBall (m+1)))).d (m+1) m
        (pushChain (Delta (m+1)) (TopCat.of (Y × MBall (m+1))) f (m+1)
          (gen (Delta (m+1)) (m+1) (idSimplex (m+1))))) :=
  ballChain_boundary_isSmall (Y := Y) m f (idSimplex (m+1))
    (fun i => isSmall_delta_push_idSimplex Y m f hbd i)

theorem pushChain_ballPair_relativeCycle (Y : Type) [TopologicalSpace Y] [Subsingleton Y]
    [Nonempty Y] (p : ℕ) (hp : 1 ≤ p)
    (f : C(stdSimplex ℝ (Fin (p+1)), TopCat.of (Y × Work.Thom.MBall p)))
    (hbd : ∀ z : stdSimplex ℝ (Fin (p+1)),
      (∃ i : Fin (p+1), (z : Fin (p+1) → ℝ) i = 0) → f z ∈ Work.Thom.DiscB Y p) :
    Work.Cohomology.IsSmallChain (Work.Thom.DiscB Y p) ∅
      ((Work.Cohomology.singularChains ℤ (TopCat.of (Y × Work.Thom.MBall p))).d p (p - 1)
        (Work.Cohomology.pushChain (Work.Cohomology.Delta p) (TopCat.of (Y × Work.Thom.MBall p))
          (TopCat.ofHom f) p
          (Work.Cohomology.gen (Work.Cohomology.Delta p) p (Work.Whitney.idSimplex p)))) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hp)
  exact pushChain_ballPair_relativeCycle_aux Y m (TopCat.ofHom f) hbd

end

end Work.Whitney

/-! ## Axiom check -/

#print axioms Work.Whitney.isSmall_delta_push_idSimplex
#print axioms Work.Whitney.pushChain_ballPair_relativeCycle
