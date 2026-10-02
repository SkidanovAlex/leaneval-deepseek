import Mathlib
import Submission.Work.Stems.rationalHurewiczStable_of_contract
import Submission.Work.Stems.WedgePinch

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The connectivity of spheres, from the geometric input

`Work.Stems.SphereConnectivity` (`Stems/rationalHurewiczStable_of_contract.lean`) is the statement
that `πᵢ(Sⁿ) = 0` for `i < n`.  It is the hypothesis of the shared contract
`Work.Drive.RationalHurewiczStable` at `X = Sⁿ`, `k = n`, hence the last input of the derivation of
`Work.Drive.StableStemsTorsion` from that contract.

This file reduces it to the single geometric statement `SphereMapNull`: **every continuous based
map of spheres `S^j → Sⁿ` with `j < n` is null-homotopic relative to its base point** — the
classical "general position" fact (`Sⁿ` has no cells below dimension `n`), which is proved
separately (`Stems/sphereMapNull.lean`) by the Sard route.

The reduction itself is the cube/sphere descent of `Work.Stems.cubeLift`: a based cube
`p : Ω^(Fin i) Sⁿ x₀` descends to a based map of spheres `Sⁱ → Sⁿ`, which the geometric statement
makes null-homotopic; descending a homotopy of the descended map through the collapse `Iⁱ → Sⁱ`
gives a homotopy of cubes.
-/

open CategoryTheory AlgebraicTopology
open scoped Topology Topology.Homotopy unitInterval

namespace Work.Stems

noncomputable section

/-- **The geometric input of the connectivity of spheres**: for `1 ≤ j < n`, every continuous map
`f : S^j → Sⁿ` is null-homotopic relative to a base point at which it takes the value `x₀`. -/
def SphereMapNull : Prop :=
  ∀ (j n : ℕ), 1 ≤ j → j < n → ∀ (b : sphere j) (x₀ : sphere n) (f : C(sphere j, sphere n)),
    f b = x₀ → ContinuousMap.HomotopicRel f (ContinuousMap.const _ x₀) {b}

/-! ## Descending a homotopy of the descended cube -/

/-- **A homotopy of the descended cube fixing the collapsed point is a homotopy of cubes.**
This is the quotient-universal property of the collapse `φ : Iⁱ → Sⁱ` (`cubeLift_comp`). -/
theorem genLoop_homotopic_const_of_homotopyRel (i n : ℕ) (hi : 1 ≤ i) (x₀ : sphere n)
    (p : Ω^ (Fin i) (sphere n) x₀)
    (H : ContinuousMap.HomotopyRel (cubeLift i hi p) (ContinuousMap.const (sphere i) x₀)
      {sphBase i hi}) :
    GenLoop.Homotopic p GenLoop.const := by
  have hfix : ∀ t : I, H (t, sphBase i hi) = x₀ := fun t => by
    rw [ContinuousMap.HomotopyRel.eq_fst H t (by simp), cubeLift_sphBase i hi p]
  refine ⟨{ toHomotopy := ?_, prop' := ?_ }⟩
  · refine ⟨⟨fun y => H (y.1, collapseMap i hi y.2), ?_⟩, ?_, ?_⟩
    · exact H.continuous.comp
        (continuous_fst.prodMk ((collapseMap i hi).continuous.comp continuous_snd))
    · intro x
      change H (0, collapseMap i hi x) = p.1 x
      rw [H.apply_zero]
      exact congrFun (congrArg DFunLike.coe (cubeLift_comp i hi p)) x
    · intro x
      change H (1, collapseMap i hi x) = GenLoop.const.1 x
      rw [H.apply_one]
      rfl
  · intro t y hy
    change H (t, collapseMap i hi y) = p.1 y
    rw [collapseMap_boundary i hi hy, show collapseMap i hi 0 = sphBase i hi from rfl, hfix t]
    exact (p.2 y hy).symm

/-! ## The reduction -/

/-- **The connectivity of spheres follows from the geometric input.** -/
theorem sphereConnectivity_of_sphereMapNull (h : SphereMapNull) : SphereConnectivity := by
  intro n i hin x₀
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · -- `i = 0`: `π₀(Sⁿ)` is trivial, i.e. `Sⁿ` is path connected (`n ≥ 1` since `i < n`)
    subst hi0
    have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
      rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
      exact_mod_cast (by omega : 1 < n + 1)
    haveI : PathConnectedSpace (sphere n) :=
      (isPathConnected_iff_pathConnectedSpace).mp
        (isPathConnected_sphere hrank 0 (by norm_num : (0 : ℝ) ≤ 1))
    exact ⟨fun a b =>
      (HomotopyGroup.pi0EquivZerothHomotopy (X := sphere n) (x := x₀)).injective
        (Subsingleton.elim _ _)⟩
  · -- `i ≥ 1`: descend the cube to a based map of spheres and use the geometric input
    have hi1 : 1 ≤ i := by omega
    have htriv : ∀ p : Ω^ (Fin i) (sphere n) x₀,
        (Quotient.mk _ p : HomotopyGroup (Fin i) (sphere n) x₀)
          = (Quotient.mk _ (GenLoop.const : Ω^ (Fin i) (sphere n) x₀)) := by
      intro p
      exact Quotient.sound (genLoop_homotopic_const_of_homotopyRel i n hi1 x₀ p
        (h i n hi1 hin (sphBase i hi1) x₀ (cubeLift i hi1 p) (cubeLift_sphBase i hi1 p)).some)
    refine ⟨fun a b => ?_⟩
    obtain ⟨p, hp⟩ := Quotient.exists_rep a
    obtain ⟨q, hq⟩ := Quotient.exists_rep b
    rw [← hp, ← hq, htriv p, htriv q]

end

end Work.Stems
