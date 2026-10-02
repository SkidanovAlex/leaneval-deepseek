import Mathlib
import Submission.Work.StemsB.HurewiczFibration
import Submission.Work.RatHurewicz.ConnectivityBridge
import Submission.Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Cofibre

/-- **The total space of a Hurewicz fibration over a path-connected base with a path-connected fibre is path connected.** Given `x ∈ E`, pick a path in `B` from `p x` to `p e₀` (the base is path connected, from `π₀(B) = 0`), lift it from `x` by the homotopy lifting property of a Hurewicz fibration at the test space `Fin 0 → I`, obtaining a path from `x` to a point of `p ⁻¹' {p e₀}`; that fibre is path connected by hypothesis, hence `x` is joined to `e₀`. -/
theorem pathConnectedSpace_E_of_fibration {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsHurewiczFibration p) (e₀ : E) (k : ℕ) (hk : 2 ≤ k)
    (hconn : ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j) (↥(p ⁻¹' {p e₀})) ⟨e₀, rfl⟩))
    (hmodel : ∀ j : ℕ, j ≤ 2 * k - 1 → j ≠ k → Subsingleton (HomotopyGroup (Fin j) B (p e₀))) :
    PathConnectedSpace E := by
  -- `π₀` of the base is trivial, so the base is path connected
  have hB : PathConnectedSpace B :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero (p e₀)
      (hmodel 0 (by omega) (by omega))
  -- `π₀` of the fibre over `p e₀` is trivial, so the fibre is path connected
  have hF : PathConnectedSpace (↥(p ⁻¹' {p e₀})) :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero ⟨e₀, rfl⟩ (hconn 0 (by omega))
  -- a Hurewicz fibration is a Serre fibration, in particular it has path lifting
  have hpS : Work.StemsB.IsSerreFibration p := hp.isSerreFibration
  -- every point of `E` is joined to the fibre over `p e₀`, hence to `e₀`
  have key : ∀ z : E, Nonempty (Path z e₀) := by
    intro z
    obtain ⟨γ⟩ := hB.joined (p z) (p e₀)
    obtain ⟨z', hz', ⟨α⟩⟩ :=
      Work.Serre.exists_path_lift_of_isSerreFibration p hpS (e := z) (b := p z) (b' := p e₀) rfl γ
    obtain ⟨β⟩ := hF.joined ⟨z', hz'⟩ ⟨e₀, rfl⟩
    exact ⟨α.trans (β.map continuous_subtype_val)⟩
  refine ⟨⟨e₀⟩, fun x y => ?_⟩
  obtain ⟨α⟩ := key x
  obtain ⟨β⟩ := key y
  exact ⟨α.trans β.symm⟩

end Work.Cofibre
