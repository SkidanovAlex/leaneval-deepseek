import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Stems.PerSimplex.prismChainBoundary
import Submission.Work.SSS.serreE1Transport
import Submission.Work.Serre.simpHomPrism
import Submission.Work.RatHurewicz.Bridge.Defs
import Submission.Work.Cohomology.HomologyPairSequence

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The fibre transport along an edge, computed by a coherent family of lifts

This file contains the *geometric* input of the `i = 0` component of the first differential of
the Serre spectral sequence (`Work.SSS.serreE1`):

> the map on fibre homology induced by an edge `σ` of the base is the parallel transport of the
> local system `b ↦ H_t(p⁻¹b)`.

For a Serre fibration `p : E → B`, a path `γ : b₀ → b₁`, and a **coherent family of lifts**
`LiftFam p γ` of the simplices of the fibre `F₀ = p⁻¹(b₀)` over the path (the data produced by the
relative cube HLP, `REFS/NOTES_LEAD_SSS.md` §1(b)), we prove

* `Work.SSS.LiftFam.spread` — the *spread* of a simplex `τ` of `F₀`: the prism chain of the graph
  of its lift `Δ_t × I → pullback p γ`, a `(t+1)`-chain of the pullback;
* `Work.SSS.LiftFam.spread_boundary` — its boundary,
  `∂ spread τ = (bottom) - (top) - spread (∂τ)` (the chain-level statement that the spread is a
  chain map of pairs to the pullback);
* `Work.SSS.LiftFam.topChain_isCycle` — the top end of a cycle is a cycle;
* `Work.SSS.transport_eq_topEnd` (file `Submission/Work/SSS/transport_eq_topEnd.lean`) —
  consequently, for every cycle `τ`, the class of the *top end* of the lift of `τ` is the
  transport of the class of `τ`: `[topEnd τ] = transportIsoPath γ [τ]`.

The last statement is exactly the naturality comparison needed for the `i = 0` component of `d¹`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval Simplicial

namespace Work.SSS

noncomputable section

/-- The standard `n`-simplex `Δ_n` (as a topological space), named locally. -/
abbrev edgeSimp (n : ℕ) : Type := ↥(stdSimplex ℝ (Fin (n + 1)))

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **A coherent family of lifts of the fibre over a path.**  For a map `p : E → B` and a path
`γ : b₀ → b₁`, this is the data of, for every continuous map `τ : Δ_t → p⁻¹(b₀)`, a lift
`G t τ : Δ_t × I → E` of the base homotopy `(z,s) ↦ γ s`, whose bottom is `τ` and whose
restrictions to the faces of `τ` are the lifts of those faces.  This is the coherence of
`REFS/NOTES_LEAD_SSS.md` §1(b). -/
structure LiftFam (p : C(E, B)) {b₀ b₁ : B} (γ : Path b₀ b₁) where
  /-- the lifted homotopies, one for every simplex of the fibre over `b₀` -/
  G : (t : ℕ) → C(edgeSimp t, (Work.StemsB.fibre p b₀)) → C(edgeSimp t × I, E)
  /-- the lift lies over the path -/
  hbase : ∀ (t : ℕ) (τ : C(edgeSimp t, (Work.StemsB.fibre p b₀))) (z : edgeSimp t) (s : I),
    p (G t τ (z, s)) = γ s
  /-- the bottom of the homotopy is the simplex itself -/
  hbot : ∀ (t : ℕ) (τ : C(edgeSimp t, (Work.StemsB.fibre p b₀))) (z : edgeSimp t),
    G t τ (z, 0) = (τ z).1
  /-- the restriction to a face of the simplex is the lift of that face -/
  hside : ∀ (t : ℕ) (τ : C(edgeSimp (t + 1), (Work.StemsB.fibre p b₀))) (i : Fin (t + 2)),
    (G (t + 1) τ).comp
        ((Work.RatHurewicz.Bridge.coface t i).prodMap (ContinuousMap.id I))
      = G t (τ.comp (Work.RatHurewicz.Bridge.coface t i))

/-! ## Naturality of the chain of a simplex -/

/-- The simplex attached to a continuous map is natural: the simplicial map induced by `g` sends
the simplex attached to `s` to the simplex attached to `g ∘ s`. -/
theorem toSSetMap_simplexOf {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (g : C(X, Y)) (n : ℕ) (s : C(edgeSimp n, X)) :
    ((TopCat.toSSet.map (TopCat.ofHom g)).app (Opposite.op (SimplexCategory.mk n)))
        (Work.RatHurewicz.Bridge.simplexOf n s)
      = Work.RatHurewicz.Bridge.simplexOf n (g.comp s) := by
  apply ((TopCat.of Y).toSSetObjEquivT (Opposite.op (SimplexCategory.mk n))).injective
  rw [Work.RatHurewicz.Bridge.toSSetObjEquiv_simplexOf]
  simp only [TopCat.toSSetObjEquivT, TopCat.toSSet]
  rfl

/-- **The chain of a simplex is natural** under a continuous map: `chainMap` sends the chain of the
simplex attached to `s` to the chain of the simplex attached to `g ∘ s`. -/
theorem chainMap_simplexOf {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (g : C(X, Y)) (n : ℕ) (s : C(edgeSimp n, X)) :
    (ModuleCat.Hom.hom ((Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of Y)
        (TopCat.ofHom g)).f n))
        (Work.Stems.simplexChain (X := X) n (Work.RatHurewicz.Bridge.simplexOf n s))
      = Work.Stems.simplexChain (X := Y) n (Work.RatHurewicz.Bridge.simplexOf n (g.comp s)) := by
  have h := congrArg (fun (gg : ModuleCat.of ℤ ℤ ⟶
      ((TopCat.toSSet.obj (TopCat.of Y)).chainComplex (ModuleCat.of ℤ ℤ)).X n) =>
        (ConcreteCategory.hom gg) (1 : ℤ))
    (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of X)) (TopCat.toSSet.obj (TopCat.of Y))
      ((TopCat.toSSet).map (TopCat.ofHom g)) (ModuleCat.of ℤ ℤ)
      (Work.RatHurewicz.Bridge.simplexOf n s))
  rw [toSSetMap_simplexOf] at h
  exact h


/-! ## The inclusions of the two end fibres into the pullback -/

/-- The inclusion of the fibre over the source of the path into the pullback of `p` along `γ`. -/
def inclSource (p : C(E, B)) {b₀ b₁ : B} (γ : Path b₀ b₁) :
    C((Work.StemsB.fibre p b₀), Work.StemsB.Pullback p γ.toContinuousMap) where
  toFun e := ⟨((e.1 : E), 0), by
    have h : p e.1 = γ 0 := e.2.trans γ.source.symm
    simpa using h⟩
  continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.prodMk continuous_const)
    (fun e => by
      have h : p e.1 = γ 0 := e.2.trans γ.source.symm
      simpa using h)

/-- The inclusion of the fibre over the target of the path into the pullback of `p` along `γ`. -/
def inclTarget (p : C(E, B)) {b₀ b₁ : B} (γ : Path b₀ b₁) :
    C((Work.StemsB.fibre p b₁), Work.StemsB.Pullback p γ.toContinuousMap) where
  toFun e := ⟨((e.1 : E), 1), by
    have h : p e.1 = γ 1 := e.2.trans γ.target.symm
    simpa using h⟩
  continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.prodMk continuous_const)
    (fun e => by
      have h : p e.1 = γ 1 := e.2.trans γ.target.symm
      simpa using h)

/-- The chain map of the inclusion of the source fibre into the pullback. -/
def sourceChainMap (p : C(E, B)) {b₀ b₁ : B} (γ : Path b₀ b₁) :
    Work.Stems.hChain (Work.StemsB.fibre p b₀) ⟶
      Work.Stems.hChain (Work.StemsB.Pullback p γ.toContinuousMap) :=
  Work.Cohomology.chainMap ℤ _ _ (TopCat.ofHom (inclSource p γ))

/-- The chain map of the inclusion of the target fibre into the pullback. -/
def targetChainMap (p : C(E, B)) {b₀ b₁ : B} (γ : Path b₀ b₁) :
    Work.Stems.hChain (Work.StemsB.fibre p b₁) ⟶
      Work.Stems.hChain (Work.StemsB.Pullback p γ.toContinuousMap) :=
  Work.Cohomology.chainMap ℤ _ _ (TopCat.ofHom (inclTarget p γ))

namespace LiftFam

variable {p : C(E, B)} {b₀ b₁ : B} {γ : Path b₀ b₁}

/-- The **top end** of the lift of a simplex of the fibre: the simplex of the fibre over `b₁`
obtained by following the lift to time `1`. -/
def topEnd (Φ : LiftFam p γ) (t : ℕ) (τ : C(edgeSimp t, (Work.StemsB.fibre p b₀))) :
    C(edgeSimp t, (Work.StemsB.fibre p b₁)) where
  toFun z := ⟨(Φ.G t τ) (z, 1), by
    have h := Φ.hbase t τ z 1
    rw [γ.target] at h
    exact h⟩
  continuous_toFun := Continuous.subtype_mk
    ((Φ.G t τ).continuous.comp (continuous_id.prodMk continuous_const))
    (fun z => by
      have h := Φ.hbase t τ z 1
      rw [γ.target] at h
      exact h)

/-- The **graph** of the lift, as a map into the pullback of `p` along `γ`. -/
def graph (Φ : LiftFam p γ) (t : ℕ) (τ : C(edgeSimp t, (Work.StemsB.fibre p b₀))) :
    C(edgeSimp t × I, Work.StemsB.Pullback p γ.toContinuousMap) where
  toFun zs := ⟨((Φ.G t τ) zs, zs.2), by
    have h := Φ.hbase t τ zs.1 zs.2
    simpa using h⟩
  continuous_toFun := Continuous.subtype_mk
    (((Φ.G t τ).continuous).prodMk continuous_snd)
    (fun zs => by
      have h := Φ.hbase t τ zs.1 zs.2
      simpa using h)

/-- The **spread** of a simplex of the fibre: the prism chain of the graph of its lift, a chain of
degree `t + 1` of the pullback (the "spread of `τ` over the edge"). -/
def spread (Φ : LiftFam p γ) (t : ℕ) (τ : C(edgeSimp t, (Work.StemsB.fibre p b₀))) :
    (Work.Stems.hChain (Work.StemsB.Pullback p γ.toContinuousMap)).X (t + 1) :=
  Work.Stems.PerSimplex.prismChain t (Φ.graph t τ)

/-- The chain of the **top end** of the lift of a simplex. -/
def topChain (Φ : LiftFam p γ) (t : ℕ) (τ : C(edgeSimp t, (Work.StemsB.fibre p b₀))) :
    (Work.Stems.hChain (Work.StemsB.fibre p b₁)).X t :=
  Work.Stems.simplexChain t (Work.RatHurewicz.Bridge.simplexOf t (Φ.topEnd t τ))

/-- **The linear extension of the spread**: the `ℤ`-linear map sending the generator of a simplex
`τ` of the fibre to the spread `Φ.spread t τ` (the prism chain of the graph of its lift). -/
def spreadLin (Φ : LiftFam p γ) (t : ℕ) :
    (Work.Stems.hChain (Work.StemsB.fibre p b₀)).X t →ₗ[ℤ]
      (Work.Stems.hChain (Work.StemsB.Pullback p γ.toContinuousMap)).X (t + 1) :=
  (Work.Cohomology.Crux33.mk (Work.Serre.singX
      (Work.StemsB.Pullback p γ.toContinuousMap)) (t + 1)).comp
    ((Finsupp.linearCombination ℤ (fun a : Work.Stems.hSimplex (Work.StemsB.fibre p b₀) t =>
        Work.Cohomology.Crux33.coords (Work.Serre.singX
            (Work.StemsB.Pullback p γ.toContinuousMap)) (t + 1)
          (Φ.spread t (((TopCat.of (Work.StemsB.fibre p b₀)).toSSetObjEquivT
            (Opposite.op (SimplexCategory.mk t))) a)))).comp
      (Work.Cohomology.Crux33.coords (Work.Serre.singX (Work.StemsB.fibre p b₀)) t))

/-- The linear extension of the spread computed on a generator. -/
theorem spreadLin_simplex (Φ : LiftFam p γ) (t : ℕ)
    (τ : C(edgeSimp t, (Work.StemsB.fibre p b₀))) :
    Φ.spreadLin t
        (Work.Stems.simplexChain (X := (Work.StemsB.fibre p b₀)) t
          (Work.RatHurewicz.Bridge.simplexOf t τ))
      = Φ.spread t τ := by
  rw [spreadLin, LinearMap.comp_apply, LinearMap.comp_apply, Work.Stems.coords_simplexChain,
    Finsupp.linearCombination_single, one_smul]
  have h := Work.RatHurewicz.Bridge.toSSetObjEquiv_simplexOf t τ
  rw [h]
  exact LinearMap.congr_fun (Work.Cohomology.Crux33.mk_comp_coords
    (Work.Serre.singX (Work.StemsB.Pullback p γ.toContinuousMap)) (t + 1)) (Φ.spread t τ)

/-- The bottom of the graph of the lift of a simplex is the inclusion of that simplex into the
pullback. -/
theorem graph_comp_botIncl (Φ : LiftFam p γ) (t : ℕ)
    (τ : C(edgeSimp t, (Work.StemsB.fibre p b₀))) :
    (Φ.graph t τ).comp (Work.Serre.botIncl t) = (inclSource p γ).comp τ := by
  ext z
  apply Subtype.ext
  apply Prod.ext
  · show (Φ.G t τ) (z, 0) = (τ z).1
    exact Φ.hbot t τ z
  · rfl

/-- The top of the graph of the lift of a simplex is the inclusion of the top end of the lift. -/
theorem graph_comp_topIncl (Φ : LiftFam p γ) (t : ℕ)
    (τ : C(edgeSimp t, (Work.StemsB.fibre p b₀))) :
    (Φ.graph t τ).comp (Work.Serre.topIncl t) = (inclTarget p γ).comp (Φ.topEnd t τ) := by
  ext z
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · rfl

/-- The restriction of the graph of the lift of a simplex to a coface is the graph of the lift of
the corresponding face. -/
theorem graph_comp_coface (Φ : LiftFam p γ) (t : ℕ)
    (τ : C(edgeSimp (t + 1), (Work.StemsB.fibre p b₀))) (i : Fin (t + 2)) :
    (Φ.graph (t + 1) τ).comp
        ((Work.RatHurewicz.Bridge.coface t i).prodMap (ContinuousMap.id I))
      = Φ.graph t (τ.comp (Work.RatHurewicz.Bridge.coface t i)) := by
  ext x
  apply Subtype.ext
  apply Prod.ext
  · have h := congrArg (fun (f : C(edgeSimp t × I, E)) => f x) (Φ.hside t τ i)
    show (Φ.G (t + 1) τ) ((Work.RatHurewicz.Bridge.coface t i) x.1, x.2)
      = (Φ.G t (τ.comp (Work.RatHurewicz.Bridge.coface t i))) (x.1, x.2)
    exact h
  · rfl

/-- The differential of the linear extension of the spread, computed on the generator of a
simplex: it is the alternating sum of the spreads of the faces. -/
theorem spreadLin_differential (Φ : LiftFam p γ) (t : ℕ)
    (τ : C(edgeSimp (t + 1), (Work.StemsB.fibre p b₀))) :
    Φ.spreadLin t
        ((ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.fibre p b₀)).d (t + 1) t))
          (Work.Stems.simplexChain (X := (Work.StemsB.fibre p b₀)) (t + 1)
            (Work.RatHurewicz.Bridge.simplexOf (t + 1) τ)))
      = ∑ i : Fin (t + 2), (-1 : ℤ) ^ (i : ℕ) •
          (Φ.spread t (τ.comp (Work.RatHurewicz.Bridge.coface t i))) := by
  have hd : (ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.fibre p b₀)).d (t + 1) t))
        (Work.Stems.simplexChain (X := (Work.StemsB.fibre p b₀)) (t + 1)
          (Work.RatHurewicz.Bridge.simplexOf (t + 1) τ))
      = ∑ i : Fin (t + 2), (-1 : ℤ) ^ (i : ℕ) •
          (Work.Stems.simplexChain (X := (Work.StemsB.fibre p b₀)) t
            (Work.RatHurewicz.Bridge.simplexOf t
              (τ.comp (Work.RatHurewicz.Bridge.coface t i)))) := by
    rw [Work.RatHurewicz.Bridge.d_ιChainComplex_one]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Work.Stems.PerSimplex.delta_simplexOf]
  rw [hd, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_zsmul, spreadLin_simplex]

/-- The chain of the bottom end of the graph of the lift of a simplex is the image of the chain of
the simplex under the inclusion of the source fibre. -/
theorem botChain_eq (Φ : LiftFam p γ) (t : ℕ)
    (τ : C(edgeSimp t, (Work.StemsB.fibre p b₀))) :
    Work.Stems.simplexChain (X := (Work.StemsB.Pullback p γ.toContinuousMap)) t
        (Work.RatHurewicz.Bridge.simplexOf t
          ((Φ.graph t τ).comp (Work.Serre.botIncl t)))
      = (ModuleCat.Hom.hom ((sourceChainMap p γ).f t))
          (Work.Stems.simplexChain (X := (Work.StemsB.fibre p b₀)) t
            (Work.RatHurewicz.Bridge.simplexOf t τ)) := by
  rw [graph_comp_botIncl Φ t τ, sourceChainMap]
  exact (chainMap_simplexOf (inclSource p γ) t τ).symm

/-- The chain of the top end of the graph of the lift of a simplex is the image of the chain of the
top end under the inclusion of the target fibre. -/
theorem topChain_eq (Φ : LiftFam p γ) (t : ℕ)
    (τ : C(edgeSimp t, (Work.StemsB.fibre p b₀))) :
    Work.Stems.simplexChain (X := (Work.StemsB.Pullback p γ.toContinuousMap)) t
        (Work.RatHurewicz.Bridge.simplexOf t
          ((Φ.graph t τ).comp (Work.Serre.topIncl t)))
      = (ModuleCat.Hom.hom ((targetChainMap p γ).f t)) (Φ.topChain t τ) := by
  rw [graph_comp_topIncl Φ t τ, targetChainMap, topChain]
  exact (chainMap_simplexOf (inclTarget p γ) t (Φ.topEnd t τ)).symm

/-- **The boundary of the spread.**  The spread of a simplex of the fibre is a chain map of pairs
from the chains of the fibre to the chains of the pullback: its boundary is the difference of the
two ends of the lift minus the spread of the boundary. -/
theorem spread_boundary (Φ : LiftFam p γ) (t : ℕ)
    (τ : C(edgeSimp (t + 1), (Work.StemsB.fibre p b₀))) :
    (ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.Pullback p γ.toContinuousMap)).d
        (t + 2) (t + 1))) (Φ.spread (t + 1) τ)
      = (ModuleCat.Hom.hom ((sourceChainMap p γ).f (t + 1)))
          (Work.Stems.simplexChain (X := (Work.StemsB.fibre p b₀)) (t + 1)
            (Work.RatHurewicz.Bridge.simplexOf (t + 1) τ))
        - (ModuleCat.Hom.hom ((targetChainMap p γ).f (t + 1))) (Φ.topChain (t + 1) τ)
        - Φ.spreadLin t
            ((ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.fibre p b₀)).d (t + 1) t))
              (Work.Stems.simplexChain (X := (Work.StemsB.fibre p b₀)) (t + 1)
                (Work.RatHurewicz.Bridge.simplexOf (t + 1) τ))) := by
  have hb := Work.Stems.PerSimplex.prismChainBoundary
    (X := Work.StemsB.Pullback p γ.toContinuousMap) t (Φ.graph (t + 1) τ)
  have hbot := botChain_eq Φ (t + 1) τ
  have htop := topChain_eq Φ (t + 1) τ
  have hsum := spreadLin_differential Φ t τ
  rw [spread, hb, hbot, htop]
  simp only [graph_comp_coface Φ t τ] at hsum ⊢
  have hsum' : (∑ i : Fin (t + 2), (-1 : ℤ) ^ (i : ℕ) •
        Work.Stems.PerSimplex.prismChain t
          (Φ.graph t (τ.comp (Work.RatHurewicz.Bridge.coface t i))))
      = Φ.spreadLin t
          ((ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.fibre p b₀)).d (t + 1) t))
            (Work.Stems.simplexChain (X := (Work.StemsB.fibre p b₀)) (t + 1)
              (Work.RatHurewicz.Bridge.simplexOf (t + 1) τ))) := hsum.symm
  rw [hsum']


/-- The linear extension of the top end map. -/
def topLin (Φ : LiftFam p γ) (t : ℕ) :
    (Work.Stems.hChain (Work.StemsB.fibre p b₀)).X t →ₗ[ℤ]
      (Work.Stems.hChain (Work.StemsB.fibre p b₁)).X t :=
  (Work.Cohomology.Crux33.mk (Work.Serre.singX (Work.StemsB.fibre p b₁)) t).comp
    ((Finsupp.linearCombination ℤ (fun a : Work.Stems.hSimplex (Work.StemsB.fibre p b₀) t =>
        Work.Cohomology.Crux33.coords (Work.Serre.singX (Work.StemsB.fibre p b₁)) t
          (Φ.topChain t (((TopCat.of (Work.StemsB.fibre p b₀)).toSSetObjEquivT
            (Opposite.op (SimplexCategory.mk t))) a)))).comp
      (Work.Cohomology.Crux33.coords (Work.Serre.singX (Work.StemsB.fibre p b₀)) t))

/-- The linear extension of the top end map computed on a generator. -/
theorem topLin_simplex (Φ : LiftFam p γ) (t : ℕ)
    (τ : C(edgeSimp t, (Work.StemsB.fibre p b₀))) :
    Φ.topLin t
        (Work.Stems.simplexChain (X := (Work.StemsB.fibre p b₀)) t
          (Work.RatHurewicz.Bridge.simplexOf t τ))
      = Φ.topChain t τ := by
  rw [topLin, LinearMap.comp_apply, LinearMap.comp_apply, Work.Stems.coords_simplexChain,
    Finsupp.linearCombination_single, one_smul]
  have h := Work.RatHurewicz.Bridge.toSSetObjEquiv_simplexOf t τ
  rw [h]
  exact LinearMap.congr_fun (Work.Cohomology.Crux33.mk_comp_coords
    (Work.Serre.singX (Work.StemsB.fibre p b₁)) t) (Φ.topChain t τ)

/-- The top end of the lift of a face of a simplex is the corresponding face of the top end. -/
theorem topEnd_comp_coface (Φ : LiftFam p γ) (t : ℕ)
    (τ : C(edgeSimp (t + 1), (Work.StemsB.fibre p b₀))) (i : Fin (t + 2)) :
    Φ.topEnd t (τ.comp (Work.RatHurewicz.Bridge.coface t i))
      = (Φ.topEnd (t + 1) τ).comp (Work.RatHurewicz.Bridge.coface t i) := by
  ext z
  apply Subtype.ext
  show (Φ.G t (τ.comp (Work.RatHurewicz.Bridge.coface t i))) (z, 1)
    = (Φ.G (t + 1) τ) ((Work.RatHurewicz.Bridge.coface t i) z, 1)
  exact (congrArg (fun (f : C(edgeSimp t × I, E)) => f (z, 1)) (Φ.hside t τ i)).symm

/-- **The top end map is a chain map.** -/
theorem topLin_differential (Φ : LiftFam p γ) (t : ℕ)
    (τ : C(edgeSimp (t + 1), (Work.StemsB.fibre p b₀))) :
    (ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.fibre p b₁)).d (t + 1) t))
        (Φ.topChain (t + 1) τ)
      = Φ.topLin t
          ((ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.fibre p b₀)).d (t + 1) t))
            (Work.Stems.simplexChain (X := (Work.StemsB.fibre p b₀)) (t + 1)
              (Work.RatHurewicz.Bridge.simplexOf (t + 1) τ))) := by
  have hd : (ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.fibre p b₀)).d (t + 1) t))
        (Work.Stems.simplexChain (X := (Work.StemsB.fibre p b₀)) (t + 1)
          (Work.RatHurewicz.Bridge.simplexOf (t + 1) τ))
      = ∑ i : Fin (t + 2), (-1 : ℤ) ^ (i : ℕ) •
          (Work.Stems.simplexChain (X := (Work.StemsB.fibre p b₀)) t
            (Work.RatHurewicz.Bridge.simplexOf t
              (τ.comp (Work.RatHurewicz.Bridge.coface t i)))) := by
    rw [Work.RatHurewicz.Bridge.d_ιChainComplex_one]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Work.Stems.PerSimplex.delta_simplexOf]
  have htop : (ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.fibre p b₁)).d (t + 1) t))
        (Φ.topChain (t + 1) τ)
      = ∑ i : Fin (t + 2), (-1 : ℤ) ^ (i : ℕ) •
          (Φ.topChain t (τ.comp (Work.RatHurewicz.Bridge.coface t i))) := by
    rw [topChain, Work.RatHurewicz.Bridge.d_ιChainComplex_one]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Work.Stems.PerSimplex.delta_simplexOf, ← topEnd_comp_coface Φ t τ i]
    rfl
  rw [htop, hd, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_zsmul, topLin_simplex]

/-- **The top end of a cycle is a cycle.** -/
theorem topChain_isCycle (Φ : LiftFam p γ) (t : ℕ)
    (τ : C(edgeSimp (t + 1), (Work.StemsB.fibre p b₀)))
    (hτ : (ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.fibre p b₀)).d (t + 1)
        ((ComplexShape.down ℕ).next (t + 1))))
        (Work.Stems.simplexChain (X := (Work.StemsB.fibre p b₀)) (t + 1)
          (Work.RatHurewicz.Bridge.simplexOf (t + 1) τ)) = 0) :
    (ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.fibre p b₁)).d (t + 1)
        ((ComplexShape.down ℕ).next (t + 1)))) (Φ.topChain (t + 1) τ) = 0 := by
  have h : (ComplexShape.down ℕ).next (t + 1) = t := ChainComplex.next_nat_succ t
  rw [h] at hτ ⊢
  rw [topLin_differential Φ t τ]
  simpa using congrArg (Φ.topLin t) hτ

end LiftFam

end

end Work.SSS
