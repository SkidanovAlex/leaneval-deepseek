import Mathlib
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.Smooth.Morse.Transport
import Submission.Work.SurgeryInvariance.API
import Submission.Work.TorusCover.ParamTorus_exists_liftOf

namespace Work.Smooth.Morse.Flow

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-- **A periodic flow of the parameter plane transports closed curves of the torus.**

`Φ` is a continuous flow of the parameter plane `ℝ²` which is equivariant under the period
lattice `2πℤ²` (`hperiod`): `Φ u (q + (2πk, 2πl)) = Φ u q + (2πk, 2πl)`.  Such a flow descends
to the surface `F = torus ψ`, and the image of a closed curve `γ` of `F` under the flow at time
`1` is again a closed curve `γ'` of `F`.

The curve `γ'` is described on the parameter plane: for a lift `L` of `γ` the parameters of `γ'`
are those of `Φ 1 ∘ L`.  In particular `t ↦ Φ 1 (L t)` is a lift of `γ'`, and by equivariance of
`Φ` it advances by the same lattice vector over one period as `L` does; hence `γ'` has the same
winding vector as `γ`. -/
theorem exists_curve_periodicFlow (ψ : Submission.Diffeo) (Φ : ℝ → ℝ × ℝ → ℝ × ℝ)
    (hcont : Continuous (Function.uncurry Φ))
    (hperiod : ∀ (u : ℝ) (q : ℝ × ℝ) (k l : ℤ),
      Φ u (q.1 + k * (2 * Real.pi), q.2 + l * (2 * Real.pi)) =
        ((Φ u q).1 + k * (2 * Real.pi), (Φ u q).2 + l * (2 * Real.pi)))
    {γ : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ)}
    (L : Work.CoreTopology.LiftOf (Work.Smooth.Morse.torus ψ) γ) :
    ∃ γ' : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ),
      (∀ t : ℝ, γ' t = (Work.Smooth.Morse.torus ψ).psi (Φ 1 (L.Θ t, L.Φ t)).1
        (Φ 1 (L.Θ t, L.Φ t)).2) ∧
      Work.SurgeryInvariance.windingOf (Work.Smooth.Morse.torus ψ) γ' = L.winding := by
  have hkey : Continuous fun t : ℝ => Φ 1 (L.Θ t, L.Φ t) :=
    hcont.comp (continuous_const.prodMk (L.contΘ.prodMk L.contΦ))
  let γ' : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ) :=
    { γ := fun t => (Work.Smooth.Morse.torus ψ).psi (Φ 1 (L.Θ t, L.Φ t)).1
        (Φ 1 (L.Θ t, L.Φ t)).2
      cont := (Work.Smooth.Morse.torus ψ).cont.comp (hkey.fst.prodMk hkey.snd)
      periodic := by
        intro t
        obtain ⟨k, l, hk, hl⟩ := L.period_shift t
        have hsh : Φ 1 (L.Θ (t + 2 * Real.pi), L.Φ (t + 2 * Real.pi)) =
            ((Φ 1 (L.Θ t, L.Φ t)).1 + k * (2 * Real.pi),
             (Φ 1 (L.Θ t, L.Φ t)).2 + l * (2 * Real.pi)) := by
          rw [hk, hl]
          exact hperiod 1 (L.Θ t, L.Φ t) k l
        show (Work.Smooth.Morse.torus ψ).psi
            (Φ 1 (L.Θ (t + 2 * Real.pi), L.Φ (t + 2 * Real.pi))).1
            (Φ 1 (L.Θ (t + 2 * Real.pi), L.Φ (t + 2 * Real.pi))).2 =
          (Work.Smooth.Morse.torus ψ).psi (Φ 1 (L.Θ t, L.Φ t)).1
            (Φ 1 (L.Θ t, L.Φ t)).2
        rw [hsh]
        exact ((Work.Smooth.Morse.torus ψ).psi_eq_iff _ _ _ _).mpr ⟨⟨k, rfl⟩, ⟨l, rfl⟩⟩
      mem := fun t => (Work.Smooth.Morse.torus ψ).psi_mem_carrier _ _ }
  have hγ'apply : ∀ t : ℝ, γ' t = (Work.Smooth.Morse.torus ψ).psi
      (Φ 1 (L.Θ t, L.Φ t)).1 (Φ 1 (L.Θ t, L.Φ t)).2 := fun t => rfl
  have hwind : Work.SurgeryInvariance.windingOf (Work.Smooth.Morse.torus ψ) γ' = L.winding := by
    let L' : Work.CoreTopology.LiftOf (Work.Smooth.Morse.torus ψ) γ' :=
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
    rw [Work.SurgeryInvariance.windingOf_eq (Work.Smooth.Morse.torus ψ) γ' L', hLL']
  exact ⟨γ', hγ'apply, hwind⟩

theorem regionEquivalent_of_periodicFlow (ψ : Submission.Diffeo) {g : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ} {a b : ℝ} (hab : a ≤ b) (Φ : ℝ → ℝ × ℝ → ℝ × ℝ) (hcont : Continuous (Function.uncurry Φ)) (hzero : ∀ q : ℝ × ℝ, Φ 0 q = q) (hperiod : ∀ (u : ℝ) (q : ℝ × ℝ) (k l : ℤ), Φ u (q.1 + k * (2 * Real.pi), q.2 + l * (2 * Real.pi)) = ((Φ u q).1 + k * (2 * Real.pi), (Φ u q).2 + l * (2 * Real.pi))) (hmaps : ∀ q : ℝ × ℝ, Work.Smooth.Morse.pullback ψ g q < b → Work.Smooth.Morse.pullback ψ g (Φ 1 q) < a) : Work.SurgeryInvariance.RegionEquivalent (Work.Smooth.Morse.torus ψ) (Work.Smooth.Morse.region ψ g a) (Work.Smooth.Morse.region ψ g b) := by
  refine ⟨?_, ?_⟩
  · intro γ hγ
    exact ⟨γ, fun t => Work.Smooth.Morse.region_mono ψ g hab (hγ t), rfl⟩
  · intro γ hγ
    obtain ⟨L⟩ := Work.TorusCover.ParamTorus_exists_liftOf (Work.Smooth.Morse.torus ψ) γ
    obtain ⟨γ', hγ'apply, hγ'wind⟩ := exists_curve_periodicFlow ψ Φ hcont hperiod L
    refine ⟨γ', ?_, ?_⟩
    · intro t
      have hb : Work.Smooth.Morse.pullback ψ g (L.Θ t, L.Φ t) < b := by
        have h1 : Work.Smooth.Morse.param ψ (L.Θ t, L.Φ t) = γ t := by
          rw [Work.Smooth.Morse.param_apply]
          exact L.lifts t
        show g (Work.Smooth.Morse.param ψ (L.Θ t, L.Φ t)) < b
        rw [h1]
        exact (hγ t).2
      have ha := hmaps (L.Θ t, L.Φ t) hb
      rw [hγ'apply t]
      exact ⟨(Work.Smooth.Morse.torus ψ).psi_mem_carrier _ _,
        by simpa [Work.Smooth.Morse.pullback] using ha⟩
    · rw [hγ'wind, Work.SurgeryInvariance.windingOf_eq (Work.Smooth.Morse.torus ψ) γ L]

end

end Work.Smooth.Morse.Flow
