import Mathlib
import Submission.Work.Serre.Engine
import Submission.Work.RatHurewicz.ConnectivityBridge
import Submission.Work.Serre.serreE2b
import Submission.Work.Serre.E2dEngine
import Submission.Work.Serre.simpHomExists
import Submission.Work.Serre.simpHomVanishing
import Submission.Work.StemsB.SerreExact

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The case `f = 0` of the Serre comparison

The Serre exact sequence in the stable range
(`Work.StemsB.relPairMap p b₀` is an isomorphism `H_i(E, p⁻¹{b₀}) ≅ H_i(B, {b₀})` for
`i < b + f`, when `B` is `(b-1)`-connected and the fibre is homologically `(f-1)`-connected)
contains the case `f = 0`: no hypothesis at all is made on the fibre, and the statement is
`H_i(E, F) ≅ H_i(B, {b₀})` for `i < b`.

In that range *both* sides vanish, and the argument is the compression property of the pair
`(B, {b₀})` (a map `(Iᵈ, ∂Iᵈ) → (B, b₀)` is null-homotopic relative to the boundary for `d ≤ b-1`,
because `π_d(B, b₀) = π_d(B) = 0`), pulled back along the fibration:

* `compressRel_singleton_of_subsingleton_pi`: the pair `(B, {b₀})` is compressible in all
  dimensions `d` with `π_d(B,b₀)` trivial;
* `compressRel_preimage_of_isSerreFibration`: the compression property of a base pair lifts along a
  Serre fibration to the pair of preimages (the same argument as
  `Work.Serre.compress_hyp_of_base_compress`, by the relative cube HLP `Work.Serre.serreE2a`);
* `serreComparison_zero`: the comparison for `f = 0`.

Note that no connectivity of the fibre is used, which is exactly why this case has to be treated
separately: the fibre of the general statement need not be connected.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-! ## 1. The pair `(B, {b₀})` is compressible below the connectivity of `B` -/

/-- **The pair `(B, {b₀})` is compressible in dimension `d` when `π_d(B, b₀)` is trivial.**
Every map of pairs `(Iᵈ, ∂Iᵈ) → (B, {b₀})` is a generalized loop, i.e. an element of
`π_d(B, b₀)`, so the triviality of the latter exhibits a homotopy relative to the boundary to the
constant map.  For `d = 0` the statement is path connectedness of `B`, i.e. the triviality of
`π₀(B, b₀)`. -/
theorem compressRel_singleton_of_subsingleton_pi {B : Type} [TopologicalSpace B] (b₀ : B) (d : ℕ)
    (h : Subsingleton (HomotopyGroup (Fin d) B b₀)) :
    Work.RatHurewicz.CompressRel B ({b₀} : Set B) d := by
  intro f hf
  -- `f` is a generalized loop, i.e. an element of `π_d(B, b₀)`
  let ψ : GenLoop (Fin d) B b₀ := ⟨f, fun y hy => by simpa using hf y hy⟩
  have hq : Quotient.mk (GenLoop.Homotopic.setoid (Fin d) b₀) ψ
      = Quotient.mk (GenLoop.Homotopic.setoid (Fin d) b₀)
          (GenLoop.const : GenLoop (Fin d) B b₀) :=
    @Subsingleton.elim _ h _ _
  have hhom : GenLoop.Homotopic ψ (GenLoop.const : GenLoop (Fin d) B b₀) := Quotient.exact hq
  obtain ⟨F⟩ := hhom
  refine ⟨swapHom F.toHomotopy.toContinuousMap, ?_, ?_, ?_⟩
  · intro x
    simp only [swapHom_apply]
    exact F.toHomotopy.apply_zero x
  · intro x hx t
    simp only [swapHom_apply]
    exact F.prop t x hx
  · intro x
    simp only [swapHom_apply, Set.mem_singleton_iff]
    exact F.toHomotopy.apply_one x

/-! ## 2. The compression property lifts along a Serre fibration -/

/-- **The compression property pulls back along a Serre fibration.**  If the pair `(B, A)` is
compressible in dimension `d`, then so is the pair `(E, p ⁻¹'A)`: given a map of pairs
`(Iᵈ, ∂Iᵈ) → (E, p⁻¹A)`, its projection to `B` is a map of pairs, which the base compression
homotopes into `A` relative to the boundary; that homotopy lifts along `p`, relative to the hat
`Iᵈ × {0} ∪ ∂Iᵈ × I`, by `Work.Serre.serreE2a`. -/
theorem compressRel_preimage_of_isSerreFibration {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) {A : Set B} (d : ℕ)
    (h : Work.RatHurewicz.CompressRel B A d) :
    Work.RatHurewicz.CompressRel E (p ⁻¹' A) d := by
  intro f hf
  -- the base map of `f`, a map of pairs `(Iᵈ, ∂Iᵈ) → (B, A)`
  let b : C(Work.Stems.Cubical.IC d, B) := p.comp f
  have hbf : ∀ t, t ∈ Cube.boundary (Fin d) → b t ∈ A := fun t ht => hf t ht
  obtain ⟨K, hK0, hKrel, hK1⟩ := h b hbf
  -- the prescribed lift on the hat: the first coordinate of the point of the cube
  let g : C(↥(hatSet d), E) := ⟨fun z => f z.1.1, by fun_prop⟩
  have hg : ∀ z : ↥(hatSet d), g z = f z.1.1 := fun _ => rfl
  have hcomp : p.comp g = K.comp (hatIncl d) := by
    ext z
    show p (f z.1.1) = K (z.1.1, z.1.2)
    rcases z.2 with hz | hz
    · -- the bottom face: the compression homotopy starts at the base map
      rw [hz, hK0]
      rfl
    · -- the lateral face: the compression homotopy is constant there
      rw [hKrel z.1.1 hz z.1.2]
      rfl
  obtain ⟨G, hG, hGhat⟩ := serreE2a E B p d hp K g hcomp
  refine ⟨⟨fun z => G (z.1, z.2), G.continuous⟩, ?_, ?_, ?_⟩
  · -- at time `0` the lift is the original map
    intro x
    have h := hGhat ⟨(x, 0), Or.inl rfl⟩
    simpa [hg, hatIncl] using h
  · -- the lift is constant on the lateral boundary
    intro x hx t
    have h := hGhat ⟨(x, t), Or.inr hx⟩
    simpa [hg, hatIncl] using h
  · -- at time `1` the lift lies over `A`
    intro x
    have h : p (G (x, 1)) = K (x, 1) := congrFun (congrArg DFunLike.coe hG) (x, 1)
    change p (G (x, 1)) ∈ A
    rw [h]
    exact hK1 x

/-! ## 3. The comparison for `f = 0` -/

/-- **The Serre comparison in the case `f = 0`.**  If `B` is `(b-1)`-connected (`b ≥ 1`) and
`p : E → B` is a Serre fibration, then `H_i(E, p⁻¹{b₀}) → H_i(B, {b₀})` is an isomorphism for
`i < b`: in that range both relative homologies vanish, by the compression property of the base
pair and of its preimage. -/
theorem serreComparison_zero {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (b₀ : B) (b : ℕ) (hb : 1 ≤ b)
    (hconn : ∀ i < b, Subsingleton (HomotopyGroup (Fin i) B b₀)) :
    ∀ i : ℕ, i < b →
      IsIso (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) i) := by
  intro i hi
  have hiM : i ≤ b - 1 := by omega
  -- the base pair is compressible below the connectivity of `B`
  have hbase : ∀ d, d ≤ b - 1 → Work.RatHurewicz.CompressRel B ({b₀} : Set B) d :=
    fun d hd => compressRel_singleton_of_subsingleton_pi b₀ d (hconn d (by omega))
  -- and so is its preimage under the fibration
  have hpre : ∀ d, d ≤ b - 1 → Work.RatHurewicz.CompressRel E (p ⁻¹' {b₀}) d :=
    fun d hd => compressRel_preimage_of_isSerreFibration p hp d (hbase d hd)
  -- hence the two relative homologies vanish in degrees `≤ b - 1`
  have hB : IsZero ((Work.Cohomology.relChains (TopCat.of B) ({b₀} : Set B)).homology i) := by
    obtain ⟨H⟩ := simpHom_of_compress (b - 1) (fun d hd => hbase d hd)
    exact simpHomVanishing H i hiM
  have hE : IsZero ((Work.Cohomology.relChains (TopCat.of E) (p ⁻¹' {b₀})).homology i) := by
    obtain ⟨H⟩ := simpHom_of_compress (b - 1) (fun d hd => hpre d hd)
    exact simpHomVanishing H i hiM
  exact Work.StemsB.isIso_of_isZero_of_isZero hE hB

end

end Work.Serre
