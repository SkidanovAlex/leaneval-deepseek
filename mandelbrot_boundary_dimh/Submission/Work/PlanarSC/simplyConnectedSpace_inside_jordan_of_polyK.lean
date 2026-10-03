import Mathlib
import Submission.Work.PlanarSC.PolyTools
import Submission.Work.PlanarSC.HullDefs
import Submission.Work.PlanarSC.BasicFacts
import Submission.Work.PlanarSC.exists_hull_dyadicPolyomino

/-!
# The inside of a Jordan curve is simply connected, from the polyomino case

Let `γ : C(Circle, ℂ)` be injective and let `U`, `V` be the two complementary components of
`Set.range γ` (open, connected, disjoint, `U` bounded, `V` unbounded, `U ∪ V = (range γ)ᶜ`).  The
target of this module is

`SimplyConnectedSpace ↥U`,

proved *from* the hypothesis `hA` that every polyomino (a nonempty finite union of closed unit
lattice squares) which is preconnected and has preconnected complement is simply connected.

The proof is the hull criterion for simple connectivity: it is enough to show that every loop `p` in
`U` is null-homotopic in `U`.  The image `K` of `p` is compact, connected and contained in `U`, so
it is contained in a *hole-free* polyomino `P ⊆ U` (`Work.PlanarSC.exists_hull_dyadicPolyomino`, the
"filling" construction); by `hA` (transported along the scaling `z ↦ z / 2ⁿ` which identifies the
level-`n` polyominoes with the unit polyominoes) `P` is simply connected, and the null-homotopy of
`p` inside `P` is one inside `U`.

The Jordan-specific input is `Work.PlanarSC.no_bounded_component_compl_U`: the inside of a Jordan
curve has no bounded complementary component.
-/

open Set

namespace Work.PlanarSC

noncomputable section

/-! ## Scaling the plane by `2^{-n}`

The scaling `dsc n : z ↦ z / 2ⁿ` is a homeomorphism of `ℂ`; it identifies the level-`n` dyadic
polyominoes (`⋃ p ∈ S, dSq n p`) with the unit polyominoes (`Work.PlanarSC.dyadicPolyomino` vs
`Commons.Topology.Plane.polyK`). -/

/-- The scaling `z ↦ z / 2ⁿ` of `ℂ`, as a homeomorphism. -/
def dscHomeomorph (n : ℕ) : ℂ ≃ₜ ℂ where
  toFun := Commons.Topology.Plane.dsc n
  invFun := Commons.Topology.Plane.dscI n
  left_inv := Commons.Topology.Plane.dscI_dsc n
  right_inv := Commons.Topology.Plane.dsc_dscI n
  continuous_toFun := Commons.Topology.Plane.continuous_dsc n
  continuous_invFun := Commons.Topology.Plane.continuous_dscI n

@[simp]
theorem dscHomeomorph_apply (n : ℕ) (z : ℂ) :
    dscHomeomorph n z = Commons.Topology.Plane.dsc n z := rfl

/-- The level-`n` polyomino of a finite index set is the image under the scaling of the unit
polyomino of the same index set. -/
theorem image_dsc_polyK (n : ℕ) (S : Finset (ℤ × ℤ)) :
    Commons.Topology.Plane.dsc n '' Commons.Topology.Plane.polyK S = dyadicPolyomino n S := by
  simp only [Commons.Topology.Plane.polyK, dyadicPolyomino, Set.image_iUnion,
    Commons.Topology.Plane.image_dsc_unitSqAt]

/-! ## Simple connectivity of level-`n` polyominoes, from the unit case -/

/-- **The polyomino hypothesis at every level.**  A level-`n` polyomino with preconnected
polyomino and preconnected complement is simply connected, provided this is known for the unit
polyominoes (`hA`): scale the plane by `2ⁿ`. -/
theorem simplyConnectedSpace_dyadicPolyomino {n : ℕ} {S : Finset (ℤ × ℤ)} (hne : S.Nonempty)
    (h1 : IsPreconnected (dyadicPolyomino n S))
    (h2 : IsPreconnected (dyadicPolyomino n S)ᶜ)
    (hA : ∀ S : Finset (ℤ × ℤ), S.Nonempty →
      IsPreconnected (Commons.Topology.Plane.polyK S) →
      IsPreconnected (Commons.Topology.Plane.polyK S)ᶜ →
      SimplyConnectedSpace ↥(Commons.Topology.Plane.polyK S)) :
    SimplyConnectedSpace ↥(dyadicPolyomino n S) := by
  have hEq : Commons.Topology.Plane.dsc n '' Commons.Topology.Plane.polyK S
      = dyadicPolyomino n S := image_dsc_polyK n S
  have h1' : IsPreconnected (Commons.Topology.Plane.polyK S) := by
    refine (Homeomorph.isPreconnected_image (dscHomeomorph n)).mp ?_
    change IsPreconnected (Commons.Topology.Plane.dsc n '' Commons.Topology.Plane.polyK S)
    rw [hEq]; exact h1
  have h2' : IsPreconnected (Commons.Topology.Plane.polyK S)ᶜ := by
    refine (Homeomorph.isPreconnected_image (dscHomeomorph n)).mp ?_
    change IsPreconnected (Commons.Topology.Plane.dsc n '' (Commons.Topology.Plane.polyK S)ᶜ)
    have hcompl : Commons.Topology.Plane.dsc n '' (Commons.Topology.Plane.polyK S)ᶜ
        = (Commons.Topology.Plane.dsc n '' Commons.Topology.Plane.polyK S)ᶜ :=
      Homeomorph.image_compl (dscHomeomorph n) _
    rw [hcompl, hEq]
    exact h2
  have hsc : SimplyConnectedSpace ↥(Commons.Topology.Plane.polyK S) := hA S hne h1' h2'
  have hsc' : IsSimplyConnected (Commons.Topology.Plane.dsc n ''
      Commons.Topology.Plane.polyK S) :=
    (Homeomorph.isSimplyConnected_image (dscHomeomorph n)).mpr hsc
  rw [hEq] at hsc'
  exact hsc'

/-! ## The main theorem -/

theorem simplyConnectedSpace_inside_jordan_of_polyK
    (hA : ∀ S : Finset (ℤ × ℤ), S.Nonempty →
      IsPreconnected (Commons.Topology.Plane.polyK S) →
      IsPreconnected (Commons.Topology.Plane.polyK S)ᶜ →
      SimplyConnectedSpace ↥(Commons.Topology.Plane.polyK S))
    {γ : C(Circle, ℂ)} (hγ : Function.Injective γ)
    {U V : Set ℂ} (hUo : IsOpen U) (hVo : IsOpen V) (hUc : IsConnected U) (hVc : IsConnected V)
    (hdisj : Disjoint U V) (hUb : Bornology.IsBounded U) (hVb : ¬ Bornology.IsBounded V)
    (hcover : U ∪ V = (Set.range γ)ᶜ) :
    SimplyConnectedSpace ↥U := by
  -- the inside of a Jordan curve has no bounded complementary component
  have hnb : ∀ z : ℂ, z ∉ U → ¬ Bornology.IsBounded (connectedComponentIn Uᶜ z) :=
    no_bounded_component_compl_U hγ hUo hVo hUc hVc hdisj hVb hcover
  change IsSimplyConnected U
  rw [isSimplyConnected_iff_exists_homotopy_refl_forall_mem]
  refine ⟨hUo.isConnected_iff_isPathConnected.mp hUc, ?_⟩
  -- every loop in `U` is null-homotopic in `U`
  intro x p hp
  set K : Set ℂ := Set.range p with hKdef
  have hKcpt : IsCompact K := isCompact_range p.continuous
  have hKconn : IsConnected K := isConnected_range p.continuous
  have hKU : K ⊆ U := by rintro z ⟨t, rfl⟩; exact hp t
  -- the loop is contained in a hole-free polyomino inside `U`
  obtain ⟨n, S, hne, hKP, hPU, hPpre, hPprec⟩ :=
    exists_hull_dyadicPolyomino hUo hnb hKcpt hKconn hKU
  haveI : SimplyConnectedSpace ↥(dyadicPolyomino n S) :=
    simplyConnectedSpace_dyadicPolyomino hne hPpre hPprec hA
  -- and there the loop is null-homotopic
  have hPs : IsSimplyConnected (dyadicPolyomino n S) :=
    (show SimplyConnectedSpace ↥(dyadicPolyomino n S) from inferInstance)
  obtain ⟨F, hF⟩ := (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp hPs).2 x p
    (fun t => hKP ⟨t, rfl⟩)
  exact ⟨F, fun t => hPU (hF t)⟩

end

end Work.PlanarSC
