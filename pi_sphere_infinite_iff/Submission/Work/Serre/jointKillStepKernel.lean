import Mathlib
import Submission.Work.Serre.E3aSkDefs
import Submission.Work.Serre.SPC.piOne_killStep
import Submission.Work.RatHurewicz.killKernelFinite

set_option synthInstance.maxHeartbeats 400000


/-!
# The `π₁`-killing step for a family of classes covering the kernel

`Work.Serre.SPC.piOne_killStep` kills `π₁(g)`: given `g : C(Γ,B)` with `g γ₀ = b₀` whose induced
map on `π₁` is *surjective*, attaching one `2`-cell along a representative loop of **every**
element of the kernel of `π₁(g)` and extending `g` over each cell produces a map whose `π₁` is
*bijective*.

Here we extract the two features of the proof that do not use the special shape
`ι = ker π₁(g)`, `φ = Subtype.val`:

* the cells are attached along the loops `killFamily 0 Γ γ₀ (φ k)` for an **arbitrary** family
  `φ : ι → π₁(Γ,γ₀)`,
* the argument only needs `φ` to take values in the kernel (`hφker`) and to **cover** the kernel
  (`hφsurj`).

This is the form needed when two maps `f : Γ → B`, `f' : Γ → B'` out of the *same* space have the
same kernel on `π₁`: the common family `φ : ι → π₁(Γ,γ₀)` (for `ι` the kernel of `π₁(f)`) covers the
kernel of `π₁(f')` as well, so both maps can be extended over the *same* attached space and both
become `π₁`-bijective.  That is the content of `Work.Serre.jointKillStepKernel` below.
-/

open scoped Topology Topology.Homotopy unitInterval
open Work.RatHurewicz

namespace Work.Serre

noncomputable section

/-- **The `π₁`-killing step for an arbitrary family covering the kernel.**

Let `g : C(Γ,B)` be based at `γ₀ ↦ b₀` and surjective on `π₁`, and let `φ : ι → π₁(Γ,γ₀)` be a
family of classes lying in the kernel of `π₁(g)` (`hφker`) which covers that kernel (`hφsurj`).
Attaching, for each `k : ι`, a `2`-cell along the loop `killFamily 0 Γ γ₀ (φ k)` and extending `g`
over it (possible because `π₁(g) (φ k) = 1`) yields a map, defined on
`attachCells 0 Γ ι (fun k => killFamily 0 Γ γ₀ (φ k))`, whose induced map on `π₁` is bijective.

The hypotheses `hbase` and `hsurj` are those of `Work.Serre.SPC.piOne_killStep`; `hbase` is not
used in the proof and is kept only to make the lemma a drop-in generalisation. -/
theorem attachG_killStep_bijective {B : Type} [TopologicalSpace B] (b₀ : B)
    {Γ : Type} [TopologicalSpace Γ] (γ₀ : Γ) (g : C(Γ, B)) (hbase : g γ₀ = b₀)
    (hsurj : Function.Surjective (piMapN g 1 γ₀)) {ι : Type}
    (φ : ι → HomotopyGroup (Fin 1) Γ γ₀)
    (hφker : ∀ k, piMapN g 1 γ₀ (φ k) = 1)
    (hφsurj : ∀ α, piMapN g 1 γ₀ α = 1 → ∃ k, φ k = α) :
    ∃ (G : ι → C(cellDisk 0, B))
      (hG : ∀ (k : ι) (z : cellSphere 0),
        G k (cellSphereToDisk 0 z) = g (killFamily 0 Γ γ₀ (φ k) z)),
      Function.Bijective (piMapN
        (Work.Serre.CWModel.attachG 0 Γ ι (fun k => killFamily 0 Γ γ₀ (φ k)) g G hG)
        1 (attachIncl 0 Γ ι (fun k => killFamily 0 Γ γ₀ (φ k)) γ₀)) := by
  classical
  let f : ι → C(cellSphere 0, Γ) := fun k => killFamily 0 Γ γ₀ (φ k)
  -- each attaching loop becomes null-homotopic after `g`, because its class lies in the kernel
  have hnull : ∀ k : ι, (g.comp (f k)).Homotopic
      (ContinuousMap.const (cellSphere 0) (g γ₀)) :=
    fun k => homotopic_const_of_piMap_eq_one g γ₀ (φ k) (hφker k)
  -- the extensions over the `2`-cells
  let G : ι → C(cellDisk 0, B) := fun k =>
    Classical.choose (Work.Serre.CWModel.sphereExtend (g.comp (f k))
      (hnull k).some.toContinuousMap (g γ₀)
      (hnull k).some.map_zero_left (hnull k).some.map_one_left)
  have hG : ∀ (k : ι) (z : cellSphere 0), G k (cellSphereToDisk 0 z) = g (f k z) := by
    intro k z
    have hspec := Classical.choose_spec (Work.Serre.CWModel.sphereExtend (g.comp (f k))
      (hnull k).some.toContinuousMap (g γ₀)
      (hnull k).some.map_zero_left (hnull k).some.map_one_left)
    exact congrFun (congrArg DFunLike.coe hspec) z
  refine ⟨G, hG, ?_⟩
  let g' : C(attachCells 0 Γ ι f, B) := Work.Serre.CWModel.attachG 0 Γ ι f g G hG
  -- functoriality: `π₁(g') ∘ π₁(incl) = π₁(g)`
  have hcomp' : ∀ a : HomotopyGroup (Fin 1) Γ γ₀,
      piMapN g 1 γ₀ a
        = piMapN g' 1 (attachIncl 0 Γ ι f γ₀) (piMapN (attachIncl 0 Γ ι f) 1 γ₀ a) :=
    fun a => piMapN_comp (attachIncl 0 Γ ι f) g' 1 γ₀ a
  -- multiplicativity of the induced maps on `π₁`
  have hmul : ∀ {Z : Type} [TopologicalSpace Z] (q : C(Γ, Z))
      (a b : HomotopyGroup (Fin 1) Γ γ₀),
      piMapN q 1 γ₀ (a * b) = piMapN q 1 γ₀ a * piMapN q 1 γ₀ b :=
    fun q a b => map_mul (Work.StemsB.πmap q 0 γ₀) a b
  have hinv : ∀ {Z : Type} [TopologicalSpace Z] (q : C(Γ, Z))
      (a : HomotopyGroup (Fin 1) Γ γ₀),
      piMapN q 1 γ₀ a⁻¹ = (piMapN q 1 γ₀ a)⁻¹ :=
    fun q a => map_inv (Work.StemsB.πmap q 0 γ₀) a
  -- every element of the kernel dies in the attached space
  have hkill : ∀ α : HomotopyGroup (Fin 1) Γ γ₀, piMapN g 1 γ₀ α = 1 →
      piMapN (attachIncl 0 Γ ι f) 1 γ₀ α = 1 := by
    intro α hα
    obtain ⟨k, hk⟩ := hφsurj α hα
    rw [← hk]
    exact Work.Serre.CWModel.killSub (n := 0) Γ γ₀ ι φ k
  have hsf : Function.Surjective (piMapN (attachIncl 0 Γ ι f) 1 γ₀) :=
    surjective_πmap_attachIncl 0 Γ ι f γ₀
  refine ⟨?_, ?_⟩
  · -- injectivity
    intro a b hab
    obtain ⟨α, rfl⟩ := hsf a
    obtain ⟨β, rfl⟩ := hsf b
    have hαβ : piMapN g 1 γ₀ α = piMapN g 1 γ₀ β := by
      rw [hcomp' α, hcomp' β]; exact hab
    have hker : piMapN g 1 γ₀ (α * β⁻¹) = 1 := by
      rw [hmul g α β⁻¹, hinv g β, hαβ, mul_inv_cancel]
    have hk := hkill (α * β⁻¹) hker
    have hthis : piMapN (attachIncl 0 Γ ι f) 1 γ₀ α
        = piMapN (attachIncl 0 Γ ι f) 1 γ₀ β := by
      refine mul_inv_eq_one.mp ?_
      rw [← hinv (attachIncl 0 Γ ι f) β, ← hmul (attachIncl 0 Γ ι f) α β⁻¹]
      exact hk
    rw [hthis]
  · -- surjectivity
    intro y
    obtain ⟨α, hα⟩ := hsurj y
    exact ⟨piMapN (attachIncl 0 Γ ι f) 1 γ₀ α, by
      rw [← hcomp' α]; exact hα⟩


/-- **Two maps with the same kernel on `π₁` can be made `π₁`-bijective on a common space.**

Given based maps `f : Skeleton → B`, `f' : Skeleton → B'` which are surjective on `π₁` and have the
*same* kernel (`hker`), the space `Γ` obtained from the skeleton by attaching one `2`-cell along a
representative loop of every element of that common kernel admits maps `g : Γ → B`, `g' : Γ → B'`
extending `f` and `f'` — and both are isomorphisms on `π₁`, because the attached loops generate
exactly the kernel and the induced maps on `π₁` are already surjective.

The construction is `Work.Serre.attachG_killStep_bijective` applied twice to the *same* family
`φ` of kernel elements (the kernel of `π₁(f)`), which covers the kernel of `π₁(f')` by `hker`. -/
theorem jointKillStepKernel
    {X : Type} [TopologicalSpace X] (pt : X)
    {B B' : Type} [TopologicalSpace B] [TopologicalSpace B'] (b : B) (b' : B')
    (f : C(Work.Serre.E3aSk.Skeleton X pt, B)) (f' : C(Work.Serre.E3aSk.Skeleton X pt, B'))
    (hb : f (Work.Serre.E3aSk.skeletonBase X pt) = b)
    (hb' : f' (Work.Serre.E3aSk.skeletonBase X pt) = b')
    (hf : Function.Surjective (Work.Serre.piMapN f 1 (Work.Serre.E3aSk.skeletonBase X pt)))
    (hf' : Function.Surjective (Work.Serre.piMapN f' 1 (Work.Serre.E3aSk.skeletonBase X pt)))
    (hker : ∀ α : HomotopyGroup (Fin 1) (Work.Serre.E3aSk.Skeleton X pt)
        (Work.Serre.E3aSk.skeletonBase X pt),
      (Work.Serre.piMapN f 1 (Work.Serre.E3aSk.skeletonBase X pt) α = 1 ↔
        Work.Serre.piMapN f' 1 (Work.Serre.E3aSk.skeletonBase X pt) α = 1)) :
    ∃ (Γ : Type) (_ : TopologicalSpace Γ) (γ₀ : Γ) (g : C(Γ, B)) (g' : C(Γ, B')),
      g γ₀ = b ∧ g' γ₀ = b' ∧
      Function.Bijective (Work.Serre.piMapN g 1 γ₀) ∧
      Function.Bijective (Work.Serre.piMapN g' 1 γ₀) := by
  classical
  let Sk := Work.Serre.E3aSk.Skeleton X pt
  let sk₀ : Sk := Work.Serre.E3aSk.skeletonBase X pt
  -- the common kernel, as an index type, and its tautological family of classes
  let ι := {α : HomotopyGroup (Fin 1) Sk sk₀ // Work.Serre.piMapN f 1 sk₀ α = 1}
  let φ : ι → HomotopyGroup (Fin 1) Sk sk₀ := fun k => k.1
  let fK : ι → C(Work.RatHurewicz.cellSphere 0, Sk) :=
    fun k => Work.RatHurewicz.killFamily 0 Sk sk₀ (φ k)
  -- the killing step for `f`: the family is the kernel itself
  obtain ⟨G, hG, hbij⟩ := attachG_killStep_bijective b sk₀ f hb hf φ
    (fun k => k.2) (fun α hα => ⟨⟨α, hα⟩, rfl⟩)
  -- the same for `f'`: the kernel of `π₁(f')` is the same by `hker`
  obtain ⟨G', hG', hbij'⟩ := attachG_killStep_bijective b' sk₀ f' hb' hf' φ
    (fun k => (hker (φ k)).mp k.2)
    (fun α hα => ⟨⟨α, (hker α).mpr hα⟩, rfl⟩)
  refine ⟨Work.RatHurewicz.attachCells 0 Sk ι fK, inferInstance,
    Work.RatHurewicz.attachIncl 0 Sk ι fK sk₀,
    Work.Serre.CWModel.attachG 0 Sk ι fK f G hG,
    Work.Serre.CWModel.attachG 0 Sk ι fK f' G' hG', ?_, ?_, ?_, ?_⟩
  · show Work.Serre.CWModel.attachG 0 Sk ι fK f G hG
        (Work.RatHurewicz.attachIncl 0 Sk ι fK (Work.Serre.E3aSk.skeletonBase X pt)) = b
    rw [Work.Serre.CWModel.attachG_incl]
    exact hb
  · show Work.Serre.CWModel.attachG 0 Sk ι fK f' G' hG'
        (Work.RatHurewicz.attachIncl 0 Sk ι fK (Work.Serre.E3aSk.skeletonBase X pt)) = b'
    rw [Work.Serre.CWModel.attachG_incl]
    exact hb'
  · exact hbij
  · exact hbij'

end

end Work.Serre
