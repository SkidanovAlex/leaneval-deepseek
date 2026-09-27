import Mathlib
import Submission.Work.Mostow.hlDefsAccess
import Submission.Work.Mostow.deepCusp

/-!
# Positive displacement rules out a vanishing Busemann cocycle

If an isometry `g` of `ℍⁿ` moves every point by at least `δ > 0` and fixes a boundary point
`ξ ∈ Sph n`, then `g` translates the horospheres at `ξ`: the Busemann cocycle
`busemann ξ (g • 0)` at `ξ` does not vanish.

Indeed, the Busemann cocycle identity (`HypIsometryProp`)
`busemann (bd g ξ) (g • u) = busemann ξ u + busemann (bd g ξ) (g • 0)` together with `bd g ξ = ξ`
shows that `busemann ξ (g • 0) = 0` would mean that `g` preserves the Busemann function of `ξ`,
i.e. preserves every horosphere at `ξ`.  By `Work.Mostow.deepCusp` the displacement
`hdist u (g • u)` is then arbitrarily small for points `u` far out on the ray to `ξ`, which
contradicts the lower bound `δ`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

theorem busemann_ne_zero_of_posDisp (n : ℕ) (hn : 2 ≤ n)
    (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n)
    (g : LeanEval.Geometry.MostowRigidity.PO n 1)
    (hpos : ∃ δ : ℝ, 0 < δ ∧ ∀ u : Submission.Mostow.E n, δ ≤ Submission.Mostow.hdist u (g • u))
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n)
    (hfix : Submission.Mostow.bd g ξ = ξ) :
    Submission.Mostow.busemann ξ (g • (0 : Submission.Mostow.E n)) ≠ 0 := by
  obtain ⟨δ, hδ0, hδ⟩ := hpos
  have hId : HypIsoData n := HypIsoData.ofProp hI
  -- suppose the cocycle at `ξ` vanishes: then `g` preserves the Busemann function of `ξ`
  intro hbus0
  have hpres : ∀ u : E n, busemann ξ (g • u) = busemann ξ u := by
    intro u
    have h := hId.busemann_cocycle g ξ u hξ
    rw [hfix, hbus0, add_zero] at h
    exact h
  -- so `g` moves points far out on the ray to `ξ` arbitrarily little
  obtain ⟨u, hu⟩ := deepCusp n hn hA hI g ξ hξ hfix hpres δ hδ0
  -- contradicting the lower bound on the displacement
  exact absurd (hδ u) (not_le.mpr hu)

end Work.Mostow
