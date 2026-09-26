import Mathlib
import Submission.Work.BoxShrink.Bubble.Basic
import Submission.Work.Smooth.Morse.Flow.regionEquivalent_of_periodicFlow

namespace Work.BoxShrink.Bubble.Flow

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-- **A periodic flow of the parameter plane transports closed curves of a parametrised torus.**

`Φ` is a continuous flow of the parameter plane `ℝ²` which is equivariant under the period
lattice `2πℤ²` (`hperiod`): `Φ u (q + (2πk, 2πl)) = Φ u q + (2πk, 2πl)`.  Such a flow descends
to the surface `F = P.carrier`, and the image of a closed curve `γ` of `F` under the flow at
time `1` is again a closed curve `γ'` of `F`.

The curve `γ'` is described on the parameter plane: for a lift `L` of `γ` the parameters of
`γ'` are those of `Φ 1 ∘ L`.  In particular `t ↦ Φ 1 (L t)` is a lift of `γ'`, and by
equivariance of `Φ` it advances by the same lattice vector over one period as `L` does; hence
`γ'` has the same winding vector as `γ`. -/
theorem exists_curve_of_periodicFlow
    (P : Work.CoreTopology.ParamTorus) (Φ : ℝ → ℝ × ℝ → ℝ × ℝ)
    (hcont : Continuous (Function.uncurry Φ))
    (hperiod : ∀ (u : ℝ) (q : ℝ × ℝ) (k l : ℤ),
      Φ u (q.1 + k * (2 * Real.pi), q.2 + l * (2 * Real.pi)) =
        ((Φ u q).1 + k * (2 * Real.pi), (Φ u q).2 + l * (2 * Real.pi)))
    {γ : Work.CoreTopology.ClosedCurve P} (L : Work.CoreTopology.LiftOf P γ) :
    ∃ γ' : Work.CoreTopology.ClosedCurve P,
      (∀ t : ℝ, γ' t = P.psi (Φ 1 (L.Θ t, L.Φ t)).1 (Φ 1 (L.Θ t, L.Φ t)).2) ∧
      Work.SurgeryInvariance.windingOf P γ' = L.winding := by
  have hkey : Continuous fun t : ℝ => Φ 1 (L.Θ t, L.Φ t) :=
    hcont.comp (continuous_const.prodMk (L.contΘ.prodMk L.contΦ))
  let γ' : Work.CoreTopology.ClosedCurve P :=
    { γ := fun t => P.psi (Φ 1 (L.Θ t, L.Φ t)).1 (Φ 1 (L.Θ t, L.Φ t)).2
      cont := P.cont.comp (hkey.fst.prodMk hkey.snd)
      periodic := by
        intro t
        obtain ⟨k, l, hk, hl⟩ := L.period_shift t
        have hsh : Φ 1 (L.Θ (t + 2 * Real.pi), L.Φ (t + 2 * Real.pi)) =
            ((Φ 1 (L.Θ t, L.Φ t)).1 + k * (2 * Real.pi),
             (Φ 1 (L.Θ t, L.Φ t)).2 + l * (2 * Real.pi)) := by
          rw [hk, hl]
          exact hperiod 1 (L.Θ t, L.Φ t) k l
        show P.psi (Φ 1 (L.Θ (t + 2 * Real.pi), L.Φ (t + 2 * Real.pi))).1
            (Φ 1 (L.Θ (t + 2 * Real.pi), L.Φ (t + 2 * Real.pi))).2 =
          P.psi (Φ 1 (L.Θ t, L.Φ t)).1 (Φ 1 (L.Θ t, L.Φ t)).2
        rw [hsh]
        exact (P.psi_eq_iff _ _ _ _).mpr ⟨⟨k, rfl⟩, ⟨l, rfl⟩⟩
      mem := fun t => P.psi_mem_carrier _ _ }
  have hγ'apply : ∀ t : ℝ, γ' t = P.psi
      (Φ 1 (L.Θ t, L.Φ t)).1 (Φ 1 (L.Θ t, L.Φ t)).2 := fun t => rfl
  have hwind : Work.SurgeryInvariance.windingOf P γ' = L.winding := by
    let L' : Work.CoreTopology.LiftOf P γ' :=
      { Θ := fun t => (Φ 1 (L.Θ t, L.Φ t)).1
        Φ := fun t => (Φ 1 (L.Θ t, L.Φ t)).2
        contΘ := hkey.fst
        contΦ := hkey.snd
        lifts := fun t => (hγ'apply t).symm }
    have hLL' : L'.winding = L.winding := by
      have hL := L.winding_spec
      have h2pi : Φ 1 (L.Θ (2 * Real.pi), L.Φ (2 * Real.pi)) =
          ((Φ 1 (L.Θ 0, L.Φ 0)).1 + (L.winding).1 * (2 * Real.pi),
           (Φ 1 (L.Θ 0, L.Φ 0)).2 + (L.winding).2 * (2 * Real.pi)) := by
        rw [hL.1, hL.2]
        exact hperiod 1 (L.Θ 0, L.Φ 0) (L.winding).1 (L.winding).2
      have h1r : ((L'.winding).1 : ℝ) * (2 * Real.pi) =
          ((L.winding).1 : ℝ) * (2 * Real.pi) := by
        have hs : (Φ 1 (L.Θ (2 * Real.pi), L.Φ (2 * Real.pi))).1 =
            (Φ 1 (L.Θ 0, L.Φ 0)).1 + (L'.winding).1 * (2 * Real.pi) :=
          L'.winding_spec.1
        have hf := congrArg Prod.fst h2pi
        linarith
      have h2r : ((L'.winding).2 : ℝ) * (2 * Real.pi) =
          ((L.winding).2 : ℝ) * (2 * Real.pi) := by
        have hs : (Φ 1 (L.Θ (2 * Real.pi), L.Φ (2 * Real.pi))).2 =
            (Φ 1 (L.Θ 0, L.Φ 0)).2 + (L'.winding).2 * (2 * Real.pi) :=
          L'.winding_spec.2
        have hf := congrArg Prod.snd h2pi
        linarith
      exact Prod.ext (by exact_mod_cast mul_right_cancel₀ Work.CoreTopology.two_pi_ne_zero h1r)
        (by exact_mod_cast mul_right_cancel₀ Work.CoreTopology.two_pi_ne_zero h2r)
    rw [Work.SurgeryInvariance.windingOf_eq P γ' L', hLL']
  exact ⟨γ', hγ'apply, hwind⟩

end

end Work.BoxShrink.Bubble.Flow
