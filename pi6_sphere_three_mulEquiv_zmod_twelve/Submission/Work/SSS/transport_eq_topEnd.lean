import Mathlib
import Submission.Work.SSS.edgeTransport
import Submission.Work.SSS.pbTransportDefs
import Submission.Work.SSS.Transport.Basic
import Submission.Work.SSS.FirstPage.HomElts
import Submission.Work.SSS.spread_boundary_apply
import Submission.Work.SSS.transportIsoPath_hom_eq
import Submission.Work.SSS.targetChainMap_comp_transportPost

/-!
# The transport of fibre homology computed by a coherent family of lifts

The target statement `Work.SSS.transport_eq_topEnd`: for a cycle `τ` of the fibre over the source of
a path, the homology class of the top end of its coherent lift `Φ : LiftFam p γ` is the parallel
transport of the class of `τ` along `γ`.  This is the naturality comparison for the `i = 0`
component of `d¹` of the Serre filtration.

The supporting definitions live in `Submission/Work/SSS/pbTransportDefs.lean`; the three inputs are
`Work.SSS.spread_boundary_apply` (the boundary of the spread of a cycle), and the two
factorisations `Work.SSS.transportIsoPath_hom_eq` and
`Work.SSS.targetChainMap_comp_transportPost` of the path transport.

The proof is the route of the statement's docstring:

* `homologyMap_source_eq_target`: the homology maps of `sourceChainMap` and `targetChainMap` agree
  on the class of `τ` and the class of the top end of its lift, because the two chain-level images
  differ by the boundary of the spread `Φ.spread t τ`;
* `transportIsoPath_apply`: the transport is `sourceChainMap` composed with the "post" factor
  `transportPost`;
* `transportPost_apply`: the "post" factor is a left inverse of the homology map of
  `targetChainMap`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.SSS

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval Simplicial

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The image of the homology class of a `cyclesMk` under the homology map of a chain map. -/
theorem homologyMap_homologypi_cyclesMk' {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L)
    (n j : ℕ) (hj : (ComplexShape.down ℕ).next n = j) (x : K.X n)
    (hx : (ModuleCat.Hom.hom (K.d n j)) x = 0)
    (hy : (ModuleCat.Hom.hom (L.d n j)) ((ModuleCat.Hom.hom (φ.f n)) x) = 0) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ n))
        ((ModuleCat.Hom.hom (K.homologyπ n)) (K.cyclesMk x j hj hx))
      = (ModuleCat.Hom.hom (L.homologyπ n)) (L.cyclesMk ((ModuleCat.Hom.hom (φ.f n)) x) j hj hy) := by
  rw [homologyMap_homologypi_C, cyclesMap_cyclesMk_C]

/-- **The source and target chain maps of the path agree on the homology classes of the cycle
`τ` and of the top end of its lift.** -/
theorem homologyMap_source_eq_target {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) {b₀ b₁ : B} (γ : Path b₀ b₁) (Φ : LiftFam p γ) (t : ℕ)
    (τ : C(edgeSimp t, Work.StemsB.fibre p b₀))
    (hτ : (ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.fibre p b₀)).d t
        ((ComplexShape.down ℕ).next t)))
        (Work.Stems.simplexChain (X := Work.StemsB.fibre p b₀) t
          (Work.RatHurewicz.Bridge.simplexOf t τ)) = 0)
    (htop : (ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.fibre p b₁)).d t
        ((ComplexShape.down ℕ).next t))) (Φ.topChain t τ) = 0) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (sourceChainMap p γ) t))
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ
          (Work.Stems.hChain (Work.StemsB.fibre p b₀)) t))
          (HomologicalComplex.cyclesMk (Work.Stems.hChain (Work.StemsB.fibre p b₀))
            (Work.Stems.simplexChain (X := Work.StemsB.fibre p b₀) t
              (Work.RatHurewicz.Bridge.simplexOf t τ)) ((ComplexShape.down ℕ).next t) rfl hτ))
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (targetChainMap p γ) t))
        ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ
          (Work.Stems.hChain (Work.StemsB.fibre p b₁)) t))
          (HomologicalComplex.cyclesMk (Work.Stems.hChain (Work.StemsB.fibre p b₁))
            (Φ.topChain t τ) ((ComplexShape.down ℕ).next t) rfl htop)) := by
  have hb := spread_boundary_apply (p := p) (γ := γ) Φ t τ hτ
  rw [homologyMap_homologypi_cyclesMk' (sourceChainMap p γ) t ((ComplexShape.down ℕ).next t) rfl _
      hτ (by rw [chainMap_comm_apply_C, hτ, map_zero]),
    homologyMap_homologypi_cyclesMk' (targetChainMap p γ) t ((ComplexShape.down ℕ).next t) rfl _
      htop (by rw [chainMap_comm_apply_C, htop, map_zero])]
  apply (homologypi_eq_iff_sub_mem_range _ t _ _).mpr
  rw [iCycles_cyclesMk_C, iCycles_cyclesMk_C, ← hb]
  exact ⟨Φ.spread t τ, rfl⟩

/-- **The pointwise form of the transport factorisation.** -/
theorem transportIsoPath_apply {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) {b₀ b₁ : B} (γ : Path b₀ b₁) (t : ℕ)
    (x : (Work.Stems.hChain (Work.StemsB.fibre p b₀)).homology t) :
    (Work.SSS.transportIsoPath p hp γ t).hom x
      = (ModuleCat.Hom.hom (transportPost p hp γ t))
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (sourceChainMap p γ) t)) x) := by
  rw [transportIsoPath_hom_eq p hp γ t]
  change (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (sourceChainMap p γ) t
        ≫ transportPost p hp γ t)) x
      = (ModuleCat.Hom.hom (transportPost p hp γ t))
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (sourceChainMap p γ) t)) x)
  rw [ModuleCat.hom_comp, LinearMap.comp_apply]
  rfl

/-- **The post factor inverts the target inclusion on homology.** -/
theorem transportPost_apply {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) {b₀ b₁ : B} (γ : Path b₀ b₁) (t : ℕ)
    (w : Work.PiS.HZ (Work.StemsB.fibre p b₁) t) :
    (ModuleCat.Hom.hom (transportPost p hp γ t))
      ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (targetChainMap p γ) t)) w) = w := by
  have h1 := congrArg (fun (φ : Work.PiS.HZ (Work.StemsB.fibre p b₁) t ⟶
      Work.PiS.HZ (Work.StemsB.fibre p b₁) t) => (ModuleCat.Hom.hom φ) w)
    (targetChainMap_comp_transportPost p hp γ t)
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  change (ModuleCat.Hom.hom (transportPost p hp γ t))
      ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap (targetChainMap p γ) t)) w) = w at h1
  exact h1

/-- **The transport computed by a coherent family of lifts.**  For a cycle `τ` of the fibre over
`b₀` (a simplex `τ` whose chain is a cycle, `hτ`), the class of the *top end* of its lift
`Φ : LiftFam p γ` is the parallel transport of the class of `τ` along `γ`.  This is the
naturality comparison for the `i = 0` component of `d¹` of the Serre filtration.

Ingredients already proved in `Submission/Work/SSS/edgeTransport.lean`:

* `Work.SSS.LiftFam.spread_boundary` : for `τ' : C(edgeSimp (s+1), F₀)`,
  `∂ (spread (s+1) τ') = sourceChainMap (gen τ') - targetChainMap (topChain (s+1) τ')
      - spreadLin s (∂ (gen τ'))`;
* `Work.SSS.LiftFam.topChain_isCycle` : `htop` holds whenever `hτ` does (for `t ≥ 1`);
* `Work.SSS.transportIsoPath p hp γ t` is *defined* in `Submission/Work/SSS/serreE1Transport.lean`
  as `(endpoint identifications) ≪≪ pullbackTransportIso ≪≪ (endpoint identifications)`, where
  `pullbackTransportIso p hp γ.toContinuousMap t` is
  `asIso (homologyMap (inclChains _ {x | pullbackSnd _ x = 0})) ≪≪
    (asIso (homologyMap (inclChains _ {x | pullbackSnd _ x = 1}))).symm`.
  `Work.SSS.sourceChainMap`/`targetChainMap` are the chain maps induced by the *homeomorphisms*
  `pullbackFibreHomeo` of the two fibres, so their homology maps are the two factors above up to
  `Work.SSS.HZHomeoIso`.

Suggested route: `cases t with | zero => ... | succ s => ...`; in the successor case use
`spread_boundary Φ s τ` (with `hτ` to kill the `spreadLin` term) to get
`sourceChainMap (gen τ) = targetChainMap (topChain t τ)` modulo boundaries, conclude equality of
the two homology classes via `HomologicalComplex.homologyπ`/`cyclesMk`, and rewrite with the
definitions of `transportIsoPath`, `sourceChainMap`, `targetChainMap` and the homeomorphism
comparison. -/
theorem transport_eq_topEnd {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) {b₀ b₁ : B} (γ : Path b₀ b₁)
    (Φ : Work.SSS.LiftFam p γ) (t : ℕ)
    (τ : C(Work.SSS.edgeSimp t, (Work.StemsB.fibre p b₀)))
    (hτ : (ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.fibre p b₀)).d t
        ((ComplexShape.down ℕ).next t)))
        (Work.Stems.simplexChain (X := (Work.StemsB.fibre p b₀)) t
          (Work.RatHurewicz.Bridge.simplexOf t τ)) = 0)
    (htop : (ModuleCat.Hom.hom ((Work.Stems.hChain (Work.StemsB.fibre p b₁)).d t
        ((ComplexShape.down ℕ).next t))) (Φ.topChain t τ) = 0) :
    (Work.SSS.transportIsoPath p hp γ t).hom
        ((HomologicalComplex.homologyπ (Work.Stems.hChain (Work.StemsB.fibre p b₀)) t)
          (HomologicalComplex.cyclesMk (Work.Stems.hChain (Work.StemsB.fibre p b₀))
            (Work.Stems.simplexChain (X := (Work.StemsB.fibre p b₀)) t
              (Work.RatHurewicz.Bridge.simplexOf t τ)) ((ComplexShape.down ℕ).next t) rfl hτ))
      = (HomologicalComplex.homologyπ (Work.Stems.hChain (Work.StemsB.fibre p b₁)) t)
          (HomologicalComplex.cyclesMk (Work.Stems.hChain (Work.StemsB.fibre p b₁))
            (Φ.topChain t τ) ((ComplexShape.down ℕ).next t) rfl htop) := by
  rw [transportIsoPath_apply p hp γ t, homologyMap_source_eq_target p γ Φ t τ hτ htop]
  exact transportPost_apply p hp γ t _

end

end Work.SSS
