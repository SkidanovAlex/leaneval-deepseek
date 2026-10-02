import Submission.Work.Stems.Hurewicz
import Submission.Work.Cohomology.KroneckerH
import Submission.Work.Cohomology.kronH_natural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Naturality of the Kronecker pairing over a Hurewicz class

This is the **first reduction step** of the Pontryagin–Thom pairing
`⟨p₁²U, α_V⟩ = (normal p₁²-number of V)` (see `Submission/Work/Tubular/PairingNotes.md`): for a
continuous map `f : X → Y`, a cube loop `p : GenLoop (Fin n) X x` and a cohomology class
`a ∈ Hⁿ(Y; ℤ)`,

  `⟨a, h(f ∘ p)⟩ = ⟨f^*(a), h(p)⟩`.

Applied to the Gauss/classifying map of a tubular neighbourhood and the collapse of `S^N`, this is
what replaces `⟨π^*(x) ⌣ U, c_*[S^N]⟩` by `⟨c^*(π^*(x) ⌣ U), h(1_{S^N})⟩`; the remaining
ingredients (the Thom-class naturality `c^*(U) = U_ν` and the local statement
`U_ν ⌢ c_*[S^N] = ±[V]`) are named in `PairingNotes.md`.

**Implementation note (import blocker, resolved in this file).**  This module deliberately does
*not* import `Work.Stems.HurewiczMapNatural`: that module reaches `Work.Stems.WedgeFstSndAux`,
which declares the *same* names as `Work.ThomBordism.PontryaginThom.WedgeIsland` — and the latter
is in the import closure of `Work.Tubular.NormalFanme`'s dependency chain
(`NormalFrame → FramesRange → Splitting → … → PontryaginThom.Item1 → Additivity →
HurewiczAdditive → WedgeIsland`).  Lean therefore refuses to have both in one environment.  The
four declarations of `HurewiczMapNatural` that are used below are re-proved here from
`Work.Stems.Hurewicz`, `Work.Stems.HurewiczSphere` and `Work.Cohomology.kronH_natural` — modules
whose closures contain neither copy of the clash.  All of them are one-line consequences of
`Work.Stems.cubeLift_comp`, `Work.Stems.hurewiczClass_natural` and `Work.Cohomology.kronH_natural`.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.Tubular

noncomputable section

open Work.Cohomology

/-! ## The cube of a postcomposed loop -/

/-- The cube obtained from a cube `p : Ω^ N X x` by postcomposing with a continuous map
`f : C(X,Y)`: the representative used by `HomotopyGroup.map`. -/
def genLoopMapC {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) {x : X}
    (p : Ω^ N X x) : Ω^ N Y (f x) :=
  ⟨f.comp p.1, fun y hy => by rw [ContinuousMap.comp_apply, p.2 y hy]⟩

@[simp] theorem genLoopMapC_apply {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} (p : Ω^ N X x) (t : I^N) : genLoopMapC f p t = f (p t) := rfl

/-- The cube lift of a postcomposed cube: postcomposition commutes with the descent along the
collapse `Iⁿ → Sⁿ`. -/
theorem cubeLift_genLoopMapC (n : ℕ) (hn : 1 ≤ n) {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) {x₀ : X} (p : Ω^ (Fin n) X x₀) :
    Work.Stems.cubeLift n hn (genLoopMapC f p) = f.comp (Work.Stems.cubeLift n hn p) := by
  ext y
  obtain ⟨q, rfl⟩ := (Work.Stems.collapseMap_isQuotientMap n hn).surjective y
  have h₁ := congrFun (congrArg DFunLike.coe
    (Work.Stems.cubeLift_comp n hn (genLoopMapC f p))) q
  have h₂ := congrFun (congrArg DFunLike.coe (Work.Stems.cubeLift_comp n hn p)) q
  simp only [ContinuousMap.comp_apply] at h₁ h₂ ⊢
  rw [h₁, h₂]
  rfl

/-- Naturality of the Hurewicz *chain* in the space. -/
theorem hurewiczChain_naturalC (n : ℕ) (hn : 1 ≤ n) {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) {x₀ : X} (p : Ω^ (Fin n) X x₀) :
    Work.Stems.hurewiczChain n hn (f x₀) (genLoopMapC f p) =
      HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)) n
        (Work.Stems.hurewiczChain n hn x₀ p) := by
  simp only [Work.Stems.hurewiczChain, cubeLift_genLoopMapC, Work.Stems.hurewiczClass_natural]

/-! ## The naturality of the Kronecker pairing -/

/-- **Naturality of the Kronecker pairing over a Hurewicz chain.**  For `f : X → Y` continuous, a
cube loop `p` and a class `a ∈ Hⁿ(Y;ℤ)`: `⟨a, h(f ∘ p)⟩ = ⟨f^*a, h(p)⟩`. -/
theorem kronH_hurewiczChain_genLoopMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) (hn : 1 ≤ n) {x : X} (p : GenLoop (Fin n) X x)
    (a : (cochainC ℤ (TopCat.toSSet.obj (TopCat.of Y))).homology n) :
    kronH ℤ (TopCat.toSSet.obj (TopCat.of Y)) n a
        (Work.Stems.hurewiczChain n hn (f x) (genLoopMapC f p))
      = kronH ℤ (TopCat.toSSet.obj (TopCat.of X)) n
          (singularCohomologyMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f) n a)
          (Work.Stems.hurewiczChain n hn x p) := by
  rw [hurewiczChain_naturalC n hn f p]
  exact kronH_natural (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f) n a
    (Work.Stems.hurewiczChain n hn x p)

end

end Work.Tubular
