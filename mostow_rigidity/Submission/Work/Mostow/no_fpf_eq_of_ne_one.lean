import Mathlib
import Submission.Work.Mostow.axisDichotomy

/-!
# At most one non-trivial element with a fixed point in `PO 1 1`

`PO 1 1` is the full isometry group of the hyperbolic line `ℍ¹`.  In the signed-distance
coordinate `sc : E 1 → ℝ` of the chart, an element `g` acts through `Phi g : ℝ → ℝ`, and
`AxisDich.Phi_form` says `Phi g` is an affine isometry of `ℝ`, hence either a translation
`x ↦ c + x` or a reflection `x ↦ c - x`.

Consequently an element of `PO 1 1` has a fixed point in `ℍ¹` if and only if it is the identity
(translation with `c = 0`) or a reflection.  Two distinct reflections `x ↦ c - x` and `x ↦ d - x`
compose to the translation `x ↦ (c - d) + x`, which is fixed point free unless `c = d`.

Hence a subgroup all of whose elements have a fixed point contains at most one non-trivial
element: `no_fpf_eq_of_ne_one`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

open AxisDich

theorem no_fpf_eq_of_ne_one
    (hA1 : Submission.Mostow.POActionProp 1) (hI1 : Submission.Mostow.HypIsometryProp 1)
    (G : Subgroup (LeanEval.Geometry.MostowRigidity.PO 1 1))
    (hnone : ∀ g ∈ G, ∃ x : Submission.Mostow.E 1, g • x = x) :
    ∀ g ∈ G, g ≠ 1 → ∀ h ∈ G, h ≠ 1 → g = h := by
  intro g hgG gne h hhG hne
  have hA : POBasic 1 := POBasic.ofProp hA1
  have hI : HypIsoData 1 := HypIsoData.ofProp hI1
  obtain ⟨x, hxg⟩ := hnone g hgG
  obtain ⟨y, hyg⟩ := hnone h hhG
  have hgfix : Phi g (sc x) = sc x := (Phi_fix_iff hI g x).mp hxg
  have hhfix : Phi h (sc y) = sc y := (Phi_fix_iff hI h y).mp hyg
  -- `g` is a translation with fixed point, hence the identity
  obtain ⟨c, hc | hc⟩ := Phi_form hI g
  · exfalso
    have hc0 : c = 0 := by rw [hc] at hgfix; linarith
    exact gne ((Phi_eq_one_iff hA hI g).mp fun t => by rw [hc, hc0, zero_add])
  -- `h` is a translation with fixed point, hence the identity
  obtain ⟨d, hd | hd⟩ := Phi_form hI h
  · exfalso
    have hd0 : d = 0 := by rw [hd] at hhfix; linarith
    exact hne ((Phi_eq_one_iff hA hI h).mp fun t => by rw [hd, hd0, zero_add])
  -- Both `g` and `h` are reflections.  Their product lies in `G`, so it has a fixed point,
  -- which forces the two reflection centres to coincide.
  have heq : ∀ t : ℝ, Phi g t = Phi h t := by
    obtain ⟨z, hzg⟩ := hnone (g * h) (G.mul_mem hgG hhG)
    have hghfix : Phi (g * h) (sc z) = sc z := (Phi_fix_iff hI (g * h) z).mp hzg
    have hcomp : Phi (g * h) (sc z) = Phi g (Phi h (sc z)) := by
      rw [Phi_mul hA g h]; rfl
    rw [hcomp, hd, hc] at hghfix
    have hcd : c = d := by linarith
    intro t
    rw [hc, hd, hcd]
  -- Equal `Phi` means equal action on `ℍ¹`, hence equal group elements.
  have hact : ∀ u : E 1, g • u = h • u := by
    intro u
    refine sc_inj hI ?_
    have h1 : sc (g • u) = Phi g (sc u) := by
      show sc (g • u) = sc (g • pt (sc u))
      rw [pt_sc u]
    have h2 : sc (h • u) = Phi h (sc u) := by
      show sc (h • u) = sc (h • pt (sc u))
      rw [pt_sc u]
    rw [h1, h2, heq]
  have h1 : g⁻¹ * h = 1 := hA.faithful _ (fun u => by
    rw [hA.mul_smul, ← hact u, ← hA.mul_smul, inv_mul_cancel, hA.one_smul])
  calc g = g * 1 := (mul_one g).symm
    _ = g * (g⁻¹ * h) := by rw [← h1]
    _ = h := by group

end Work.Mostow
