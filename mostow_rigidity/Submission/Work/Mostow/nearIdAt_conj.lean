import Submission.Work.Mostow.QIDefs
import Submission.Mostow.HLDefs

/-!
# `nearIdAt_conj`: `NearIdAt` is invariant under conjugation of the base point

`NearIdAt g z η` says that `g` moves every point of the unit `hdist`-ball about `z` by `< η`.
It is a statement purely about the action of `PO n 1` on `ℍⁿ`, so it is transported by the action:

`NearIdAt (g⁻¹ * a * g) z η ↔ NearIdAt a (g • z) η`.

Both directions use only that `•` is an action (`POActionProp`) and that `g` is an isometry
(`HypIsometryProp`): `(g⁻¹ * a * g) • u = g⁻¹ • (a • (g • u))` and
`hdist u (g⁻¹ • v) = hdist (g • u) v`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

noncomputable section

theorem nearIdAt_conj (n : ℕ) (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n)
    (g a : LeanEval.Geometry.MostowRigidity.PO n 1) (z : Submission.Mostow.E n) (η : ℝ) :
    Submission.Mostow.NearIdAt (g⁻¹ * a * g) z η ↔ Submission.Mostow.NearIdAt a (g • z) η := by
  have hb := POBasic.ofProp hA
  have hid := HypIsoData.ofProp hI
  -- the conjugated element acts as `g⁻¹ (a (g ·))`
  have hconj : ∀ u : E n, (g⁻¹ * a * g) • u = g⁻¹ • (a • (g • u)) := by
    intro u
    rw [hb.mul_smul (g⁻¹ * a) g u, hb.mul_smul g⁻¹ a (g • u)]
  -- `g` undoes `g⁻¹`
  have hgapp : ∀ u : E n, g • (g⁻¹ • u) = u := by
    intro u; rw [← hb.mul_smul g g⁻¹ u, mul_inv_cancel, hb.one_smul]
  constructor
  · -- `g⁻¹ a g` near-identity at `z` ⟹ `a` near-identity at `g • z`
    intro h u hu
    have hu' : hdist z (g⁻¹ • u) ≤ 1 := by
      have h1 : hdist z (g⁻¹ • u) = hdist (g • z) (g • (g⁻¹ • u)) :=
        (hid.isom_smul g z (g⁻¹ • u)).symm
      rw [h1, hgapp u]
      exact hu
    have h2 := h (g⁻¹ • u) hu'
    have h3 : (g⁻¹ * a * g) • (g⁻¹ • u) = g⁻¹ • (a • u) := by
      rw [hconj (g⁻¹ • u), hgapp u]
    rw [h3] at h2
    have h4 : hdist u (a • u) = hdist (g⁻¹ • u) (g⁻¹ • (a • u)) :=
      (hid.isom_smul g⁻¹ u (a • u)).symm
    rwa [h4]
  · -- `a` near-identity at `g • z` ⟹ `g⁻¹ a g` near-identity at `z`
    intro h u hu
    have hu' : hdist (g • z) (g • u) ≤ 1 := by
      rw [hid.isom_smul g z u]
      exact hu
    have h2 := h (g • u) hu'
    have h3 : (g⁻¹ * a * g) • u = g⁻¹ • (a • (g • u)) := hconj u
    rw [h3]
    have h4 : hdist u (g⁻¹ • (a • (g • u))) = hdist (g • u) (a • (g • u)) := by
      rw [← hid.isom_smul g u (g⁻¹ • (a • (g • u))), hgapp (a • (g • u))]
    rw [h4]
    exact h2

end

end Work.Mostow
