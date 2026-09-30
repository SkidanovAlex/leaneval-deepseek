import Mathlib
import Submission.Work.Pi6.MSSK.LastEdge
import Submission.Work.Pi6.MSSK.CapThetaBasic
import Submission.Work.Pi6.MSSK.backFace_mem_edge
import Submission.Work.Cohomology.CapProduct
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The cap product with `lastFaceTop` lies over the last edge

For `p : C(E, B)`, a simplex `σ : Δ[t+1] ⟶ Sing B` and
`T_σ = Δ[t+1] ×_{Sing B} Sing E` (`Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ`), the cochain
`lastFaceTop R p σ` (`CapThetaBasic.lean`) is the `t`-cochain on `T_σ` which is `1` exactly on the
simplices whose front `t`-face is the top simplex of the *last* face of `Δ[t+1]`, i.e. whose
projection to `Δ[t+1]` fixes the vertices `0, …, t`.

**Theorem (`capLastFaceTop_edgeIncl`).** Capping any `(t + (K+1))`-chain `c` of `T_σ` with
`lastFaceTop` gives a `(K+1)`-chain of `T_σ` which lies in the image of the push-forward along

`edgeIncl p σ : T_{lastEdge t ≫ σ} ⟶ T_σ`,

the inclusion of the part of `T_σ` over the last edge `{t, t+1}` of `Δ[t+1]`.

This is the *edge* step of the cap/transport computation (`REFS/NOTES_LEAD_MSSK.md`, §1): the cap
product `lastFaceTop ⌢ c` only sees the `(K+1)`-simplices whose projection is constant `t` or lands
in `{t, t+1}`, and on those it is the value of a chain on the edge piece.

The proof is the exact analogue of `fibreIncCapThetaLift.lean` (the `thetaTop`/`fibreInc` version,
which produces the lift to the fibre over the *last vertex*).  Here :

* `EdgeCond p σ w` is the condition on a simplex `w` of `T_σ` under which its back face lies over
  the last edge (front `t`-face of the projection = last face of `Δ[t+1]`);
* `edgeBackLift` is the lift of a single such simplex, supplied by the child lemma
  `backFace_mem_edge` (the edge analogue of `backFace_mem_fibre`);
* `edgeLift` is the resulting chain-level section of `edgeIncl_*`, defined through the coproduct
  universal property `SSet.isColimitChainComplexXCofan` exactly as `capThetaLift'`;
* `capEdgeChain` identifies `edgeLift ≫ edgeIncl_*` with `capHom lastFaceTop` on the generators,
  and the theorem follows by evaluating at `c`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Work.Pi6.MSSK

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **The edge condition.**  A simplex `w` of `T_σ` of dimension `t + (K+1)` satisfies `EdgeCond`
when its front `t`-face is the last face of `Δ[t+1]`, i.e. when the underlying monotone map of its
projection `proj p σ w : Δ[t+1]_{t+K+1}` fixes the vertices `0, …, t`.

This is exactly the condition under which the cap product `lastFaceTop ⌢ ·` sees `w`. -/
def EdgeCond (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    {K : ℕ} (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋t + (K+1)⦌) : Prop :=
  Work.Cohomology.frontIncl t (t + (K+1)) (Nat.le_add_right t (K+1))
      ≫ SSet.stdSimplex.objEquiv (Work.Pi6.MSSK.proj p σ w)
    = SimplexCategory.δ (n := t) (Fin.last (t+1))

/-- **`lastFaceVal` of the front `t`-face is `1` exactly when `EdgeCond` holds.**  (The dichotomy
`0`/`1` is proved through the defining `if` of `lastFaceVal`.) -/
lemma lastFaceVal_frontFace_eq_one_iff_cond (R : Type) [CommRing R] [Nontrivial R]
    (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    {K : ℕ} (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋t + (K+1)⦌) :
    Work.Pi6.MSSK.lastFaceVal R p σ (Work.Cohomology.frontFace
        (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) t (t + (K+1))
        (Nat.le_add_right t (K+1)) w) = 1
      ↔ EdgeCond p σ w := by
  have hmap : SSet.stdSimplex.objEquiv (Work.Cohomology.frontFace
        (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) t (t + (K+1))
        (Nat.le_add_right t (K+1))
        ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋t+(K+1)⦌) w))
      = Work.Cohomology.frontIncl t (t + (K+1)) (Nat.le_add_right t (K+1))
        ≫ SSet.stdSimplex.objEquiv
            ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋t+(K+1)⦌) w) := by
    rw [Work.Cohomology.frontFace, SSet.stdSimplex.map_apply, Quiver.Hom.unop_op,
      Equiv.apply_symm_apply]
  have hiff : ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋t⦌) (Work.Cohomology.frontFace
        (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) t (t + (K+1))
        (Nat.le_add_right t (K+1)) w)
        = SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ (n := t) (Fin.last (t+1))))
      ↔ EdgeCond p σ w := by
    rw [show (pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋t⦌) (Work.Cohomology.frontFace
        (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) t (t + (K+1))
        (Nat.le_add_right t (K+1)) w)
      = Work.Cohomology.frontFace (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0})
          t (t + (K+1)) (Nat.le_add_right t (K+1))
          ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋t+(K+1)⦌) w) from
      NatTrans.naturality_apply (pullback.fst σ (Work.SSSR.sSingP p))
        (Work.Cohomology.frontIncl t (t + (K+1)) (Nat.le_add_right t (K+1))).op w,
      Equiv.eq_symm_apply, hmap]
    simp only [EdgeCond, Work.Pi6.MSSK.proj]
  have hraw : ((if (pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋t⦌)
        (Work.Cohomology.frontFace (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) t (t + (K+1))
          (Nat.le_add_right t (K+1)) w)
        = SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ (n := t) (Fin.last (t+1)))
        then (1:R) else 0) = 1)
      ↔ ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋t⦌) (Work.Cohomology.frontFace
        (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) t (t + (K+1))
        (Nat.le_add_right t (K+1)) w)
        = SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ (n := t) (Fin.last (t+1)))) := by
    by_cases h : (pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋t⦌) (Work.Cohomology.frontFace
        (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) t (t + (K+1))
        (Nat.le_add_right t (K+1)) w)
        = SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ (n := t) (Fin.last (t+1))) <;> simp [h]
  rw [Work.Pi6.MSSK.lastFaceVal, hraw]
  exact hiff

/-- `lastFaceVal` takes only the values `1` and `0`. -/
lemma lastFaceVal_eq_one_or_zero (R : Type) [CommRing R] [Nontrivial R]
    (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (y : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋t⦌) :
    Work.Pi6.MSSK.lastFaceVal R p σ y = 1 ∨ Work.Pi6.MSSK.lastFaceVal R p σ y = 0 := by
  rw [Work.Pi6.MSSK.lastFaceVal]
  split_ifs <;> simp

/-- **The lift of a single edge-cond simplex** (chosen through the child lemma
`backFace_mem_edge`). -/
def edgeBackLift (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    {K : ℕ} (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋t + (K+1)⦌)
    (h : EdgeCond p σ w) :
    (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
      (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ)) _⦋K+1⦌ :=
  Classical.choose (backFace_mem_edge p σ w h)

/-- The defining property of the lift: `edgeIncl` sends it to the back face of `w`. -/
lemma edgeBackLift_spec (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    {K : ℕ} (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋t + (K+1)⦌)
    (h : EdgeCond p σ w) :
    (Work.Pi6.MSSK.edgeIncl p σ).app (op ⦋K+1⦌) (edgeBackLift p σ w h)
      = Work.Cohomology.backFace (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) t (K+1) w :=
  Classical.choose_spec (backFace_mem_edge p σ w h)

/-- **The chain-level lift of the cap product with `lastFaceTop`:** the section of `edgeIncl_*`
which lifts `lastFaceTop ⌢ ·` back to the edge piece.  A generator is sent to its chosen lift when
it satisfies `EdgeCond` (the case in which the cap product can be non-zero) and to `0` otherwise. -/
def edgeLift (R : Type) [CommRing R] [Nontrivial R] (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) (K : ℕ) :
    (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X (t + (K+1)) ⟶
      (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ))).X (K+1) := by
  classical
  exact ((Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).isColimitChainComplexXCofan
      (ModuleCat.of R R) (t + (K+1))).desc
    (Cofan.mk ((Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ))).X (K+1))
      (fun w => if h : EdgeCond p σ w
        then (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
          (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ)).ιChainComplex
            (R := ModuleCat.of R R) (edgeBackLift p σ w h)
        else 0))

/-- **The value of `edgeLift` on a generator, `EdgeCond` case.** -/
lemma edgeLift_iota_top (R : Type) [CommRing R] [Nontrivial R] (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (K : ℕ) (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋t + (K+1)⦌)
    (h : EdgeCond p σ w) :
    (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).ιChainComplex (R := ModuleCat.of R R) w
        ≫ (edgeLift R p σ K)
      = (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
          (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ)).ιChainComplex
            (R := ModuleCat.of R R) (edgeBackLift p σ w h) := by
  classical
  rw [edgeLift]
  exact (Cofan.IsColimit.fac
    ((Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).isColimitChainComplexXCofan
      (ModuleCat.of R R) (t+(K+1)))
    (fun w => if h : EdgeCond p σ w
      then (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ)).ιChainComplex
          (R := ModuleCat.of R R) (edgeBackLift p σ w h)
      else 0) w).trans (dif_pos h)

/-- **The value of `edgeLift` on a generator, non-`EdgeCond` case**: it is `0`. -/
lemma edgeLift_iota_bot (R : Type) [CommRing R] [Nontrivial R] (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (K : ℕ) (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋t + (K+1)⦌)
    (h : ¬ EdgeCond p σ w) :
    (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).ιChainComplex (R := ModuleCat.of R R) w
        ≫ (edgeLift R p σ K) = 0 := by
  classical
  rw [edgeLift]
  refine (Cofan.IsColimit.fac
    ((Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).isColimitChainComplexXCofan
      (ModuleCat.of R R) (t+(K+1)))
    (fun w => if h : EdgeCond p σ w
      then (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ)).ιChainComplex
          (R := ModuleCat.of R R) (edgeBackLift p σ w h)
      else 0) w).trans ?_
  exact dif_neg h

/-- **The chain-level identity**: `edgeLift` is a section of the push-forward along `edgeIncl` onto
the image of the cap product with `lastFaceTop`.  Both sides are compared on the generators `ι w` of
the `(t + (K+1))`-chains of `T_σ`. -/
theorem capHom_lastFaceTop_eq_edgeLift (R : Type) [CommRing R] [Nontrivial R] (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (K : ℕ) :
    (edgeLift R p σ K) ≫ (Work.SSSR.sCCMap R (Work.Pi6.MSSK.edgeIncl p σ)).f (K+1)
      = Work.Cohomology.capHom R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
          (Work.Pi6.MSSK.lastFaceTop R p σ) (K+1) := by
  apply SSet.chainComplex_hom_ext
  intro w
  by_cases h : EdgeCond p σ w
  · -- `EdgeCond` case: the lift lands on the back face, and `lastFaceVal` is `1`
    rw [← Category.assoc, edgeLift_iota_top R p σ K w h]
    rw [show (Work.SSSR.sCCMap R (Work.Pi6.MSSK.edgeIncl p σ)).f (K+1)
        = (SSet.chainComplexMap (Work.Pi6.MSSK.edgeIncl p σ) (ModuleCat.of R R)).f (K+1)
        from rfl]
    rw [SSet.ι_chainComplexMap_f, edgeBackLift_spec p σ w h,
      Work.Cohomology.ιChainComplex_capHom, Work.Pi6.MSSK.genEval_lastFaceTop,
      (lastFaceVal_frontFace_eq_one_iff_cond R p σ w).2 h,
      show LinearMap.toSpanSingleton R R (1:R) = LinearMap.id from by ext; simp,
      ModuleCat.ofHom_id, Category.id_comp]
  · -- non-`EdgeCond` case: both sides vanish
    rw [← Category.assoc, edgeLift_iota_bot R p σ K w h, zero_comp,
      Work.Cohomology.ιChainComplex_capHom, Work.Pi6.MSSK.genEval_lastFaceTop]
    have h0 : Work.Pi6.MSSK.lastFaceVal R p σ (Work.Cohomology.frontFace
        (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) t (t + (K+1))
        (Nat.le_add_right t (K+1)) w) = 0 := by
      rcases lastFaceVal_eq_one_or_zero R p σ _ with h1 | h0
      · exact absurd ((lastFaceVal_frontFace_eq_one_iff_cond R p σ w).1 h1) h
      · exact h0
    rw [h0, show LinearMap.toSpanSingleton R R (0:R) = 0 from by ext; simp,
      ModuleCat.ofHom_zero, zero_comp]

theorem capLastFaceTop_edgeIncl (R : Type) [CommRing R] [Nontrivial R] {E B : Type}
    [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) {t K : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (c : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X (t + (K+1))) :
    ∃ ye : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (CategoryTheory.CategoryStruct.comp (Work.Pi6.MSSK.lastEdge t) σ))).X (K+1),
      (Work.SSSR.sCCMap R (Work.Pi6.MSSK.edgeIncl p σ)).f (K+1) ye
        = Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
            (Work.Pi6.MSSK.lastFaceTop R p σ) (K+1) c := by
  refine ⟨(edgeLift R p σ K).hom c, ?_⟩
  have h2 := congrArg (fun g => (ConcreteCategory.hom g) c) (capHom_lastFaceTop_eq_edgeLift R p σ K)
  simpa only [Work.Cohomology.cap, ModuleCat.hom_comp, LinearMap.comp_apply] using h2

end

end Work.Pi6.MSSK
