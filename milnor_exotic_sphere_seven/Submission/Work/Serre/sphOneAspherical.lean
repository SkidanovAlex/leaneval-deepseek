import Mathlib
import Submission.Work.Serre.Defs
import Submission.Work.Serre.C1SphOne
import Submission.Work.StemsB.fibration_les
import Submission.Work.StemsB.isSerreFibration_of_isCoveringMap
import Submission.Work.StemsB.exists_lift_rel
import Submission.Work.StemsB.pi_contractible

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `S¹` is aspherical: `π_n(S¹) = 0` for `n ≥ 2`

This is the last of the three circle facts needed by `Work.Serre.SerreC1`
(see `Submission/Work/Serre/C1SphOne.lean`): the circle `Sph 1` has no higher homotopy.

The route is the universal covering `p : ℝ → S¹ = Sph 1` (`sphOneCover =
circleHomeoSphereOne ∘ Circle.exp`):

* `ℝ` is contractible, so `π_n(ℝ) = 0` (`Work.StemsB.pi_contractible`);
* `ℝ → S¹` is a covering map, hence a Serre fibration
  (`Work.StemsB.isSerreFibration_of_isCoveringMap`), so it has a long exact homotopy sequence
  (`Work.StemsB.fibration_les`) with fibre the (discrete) fibre `p ⁻¹' {x}`;
* the fibre of a covering map is discrete (`IsEvenlyCovered.discreteTopology_fiber`), and a
  generalized loop in a discrete space is constant, so `π_k(fibre) = 0` for `k ≥ 1`.

Exactness of `π_{n}(ℝ) → π_{n}(S¹) → π_{n-1}(fibre)` then exhibits `π_n(S¹)` (`n ≥ 2`) as a
subgroup of a trivial group.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.Serre

noncomputable section

/-- The universal covering map `ℝ → S¹`, built from the quotient covering `Circle.exp` and the
homeomorphism `Circle ≃ₜ Sph 1`. -/
def sphOneCover : C(ℝ, Sph 1) :=
  ⟨fun t => circleHomeoSphereOne (Circle.exp t),
    circleHomeoSphereOne.continuous.comp Circle.exp.continuous⟩

/-- **`ℝ → S¹` is a covering map** (it is `Circle.exp` followed by a homeomorphism). -/
theorem isCoveringMap_sphOneCover : IsCoveringMap sphOneCover :=
  Circle.isCoveringMap_exp.homeomorph_comp circleHomeoSphereOne

/-- **`ℝ → S¹` is surjective** (a covering map onto a nonempty space, here transported from the
surjectivity of `Circle.exp` and of the homeomorphism `Circle ≃ₜ Sph 1`). -/
theorem sphOneCover_surjective : Function.Surjective sphOneCover := by
  intro x
  obtain ⟨c, hc⟩ := circleHomeoSphereOne.surjective x
  obtain ⟨t, ht⟩ := Circle.exp_surjective c
  exact ⟨t, by simp [sphOneCover, ht, hc]⟩

/-- **Homotopy groups of a discrete space are trivial in positive degrees.**  For `k ≥ 1`, the cube
`I^k` is preconnected, so a generalized loop `I^k → Y` into a discrete space `Y` is constant, and
since the boundary of `I^k` is nonempty the constant is the base point: every generalized loop is
literally `GenLoop.const`, so the quotient `π_k(Y,y)` is a subsingleton. -/
theorem subsingleton_homotopyGroup_of_discrete (k : ℕ) (hk : 1 ≤ k)
    (Y : Type) [TopologicalSpace Y] [DiscreteTopology Y] (y : Y) :
    Subsingleton (HomotopyGroup (Fin k) Y y) := by
  have hconst : ∀ p : Ω^ (Fin k) Y y, p = GenLoop.const := by
    intro p
    ext z
    rw [GenLoop.const_apply]
    have hz : (fun _ : Fin k => (0 : I)) ∈ Cube.boundary (Fin k) := ⟨⟨0, hk⟩, Or.inl rfl⟩
    exact (PreconnectedSpace.constant (Y := Y) inferInstance p.1.continuous
        (x := z) (y := fun _ => (0 : I))).trans (p.2 _ hz)
  refine ⟨fun a b => ?_⟩
  refine Quotient.inductionOn₂ a b (fun p q => ?_)
  rw [hconst p, hconst q]

theorem sphOneAspherical (n : ℕ) (hn : 2 ≤ n) (x : Work.Serre.Sph 1) :
    Subsingleton (HomotopyGroup (Fin n) (Work.Serre.Sph 1) x) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  -- a point of the fibre over the base point
  obtain ⟨e₀, he₀⟩ := sphOneCover_surjective x
  subst he₀
  -- the fibre of the covering map is discrete
  haveI : DiscreteTopology (Work.StemsB.fibre sphOneCover (sphOneCover e₀)) :=
    (isCoveringMap_sphOneCover (sphOneCover e₀)).discreteTopology_fiber
  haveI : Subsingleton
      (HomotopyGroup (Fin (m + 1)) (Work.StemsB.fibre sphOneCover (sphOneCover e₀))
        (Work.StemsB.fibrePoint sphOneCover e₀)) :=
    subsingleton_homotopyGroup_of_discrete (m + 1) (by omega) _ _
  -- the total space `ℝ` is contractible
  haveI : Subsingleton (HomotopyGroup (Fin (m + 2)) ℝ e₀) :=
    Work.StemsB.pi_contractible (m + 1) e₀
  -- the long exact homotopy sequence of the covering
  have hserre : Work.StemsB.IsSerreFibration sphOneCover :=
    Work.StemsB.isSerreFibration_of_isCoveringMap sphOneCover isCoveringMap_sphOneCover
  have hles : Work.StemsB.FibrationLES sphOneCover e₀ :=
    Work.StemsB.fibration_les sphOneCover
      (fun k => Work.StemsB.exists_lift_rel sphOneCover hserre k) e₀
  obtain ⟨d, -, hex, -⟩ := hles m
  -- exactness at `π_{m+2}(S¹)`: the kernel of `d` is the image of `π_{m+2}(ℝ) = 0`
  have key : ∀ y : HomotopyGroup (Fin (m + 2)) (Sph 1) (sphOneCover e₀), y = 1 := by
    intro y
    have hdy : d y = 1 := Subsingleton.elim _ _
    obtain ⟨z, hz⟩ := (hex y).mp hdy
    rw [← hz]
    exact (congrArg (Work.StemsB.πmap sphOneCover (m + 1) e₀)
      (Subsingleton.elim z 1)).trans (map_one (Work.StemsB.πmap sphOneCover (m + 1) e₀))
  exact ⟨fun a b => by rw [key a, key b]⟩

end

end Work.Serre
