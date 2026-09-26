import Mathlib
import Submission.Work.InnermostDisk.Defs
import Submission.Work.TorusCover.Main
import Submission.Work.InnermostDisk.isEssential_iff_hasWinding
import Submission.Work.InnermostDisk.homotopic_iff_homotopicClosed
import Submission.Work.InnermostDisk.isEssential_iff_of_homotopic
import Submission.Work.InnermostDisk.not_isEssential_of_const

/-!
# Inessential loops of a torus are exactly the null-homotopic ones

For a closed curve `γ` of the surface `F = P.carrier` of a parametrised torus `P`, the
following are equivalent:

* `γ` is inessential (`¬ IsEssential P γ`, i.e. its winding vector vanishes), and
* `γ` is homotopic through closed curves of `F` to a constant curve of `F`.

The equivalence is the topological statement that *the winding vector is a complete invariant
of the free homotopy class of closed curves of the torus*; here `F` is not assumed to be
compatible with any metric data (the notion of "essential" used is the purely combinatorial
one: the existence of a lift to the parameter plane whose parameters do not return to
themselves after one period).

The forward direction is constructive: a lift `L` of `γ` whose winding vector vanishes is
`2π`-periodic (`period_eq_of_winding_eq_zero`), so the straight-line interpolation of `L` to
the constant parameter value `(L.Θ 0, L.Φ 0)` descends through the parametrisation to a
homotopy of closed curves from `γ` to the constant curve at `P.psi (L.Θ 0) (L.Φ 0)`
(`homotopic_const_of_winding_eq_zero`).  The backward direction uses that the constant curve is
inessential (`not_isEssential_of_const`) and that essentiality is a homotopy invariant
(`isEssential_iff_of_homotopic`).
-/

namespace Work.InnermostDisk

open LeanEval.KnotTheory.PardonDistortion Set
open Work.CoreTopology

noncomputable section

/-- **A lift of a closed curve with vanishing winding vector is `2π`-periodic.**  The two
parameter functions of the lift return to their starting values after every period. -/
theorem period_eq_of_winding_eq_zero {P : ParamTorus} {γ : ClosedCurve P} (L : LiftOf P γ)
    (hw : L.winding = (0, 0)) :
    ∀ t : ℝ, L.Θ (t + 2 * Real.pi) = L.Θ t ∧ L.Φ (t + 2 * Real.pi) = L.Φ t := by
  intro t
  obtain ⟨h1, h2⟩ := L.period_shift_winding t
  rw [hw] at h1 h2
  exact ⟨by simpa using h1, by simpa using h2⟩

/-- **A closed curve with vanishing winding vector is null-homotopic in the torus.**

Given a lift `L` of `γ` whose winding vector vanishes, the lift is `2π`-periodic, so the
straight-line interpolation in the parameter plane between `L` and the constant value
`(L.Θ 0, L.Φ 0)` is still `2π`-periodic; composed with the parametrisation it gives a homotopy
of closed curves of `F` from `γ` to the constant curve at the point `P.psi (L.Θ 0) (L.Φ 0)`. -/
theorem homotopic_const_of_winding_eq_zero {P : ParamTorus} {γ : ClosedCurve P} (L : LiftOf P γ)
    (hw : L.winding = (0, 0)) :
    ∃ (x : R3) (hx : x ∈ P.carrier), Homotopic P γ (constCurve P x hx) := by
  have hper := period_eq_of_winding_eq_zero L hw
  refine ⟨P.psi (L.Θ 0) (L.Φ 0), P.psi_mem_carrier _ _, ?_⟩
  refine ⟨fun s t => P.psi ((1 - s) * L.Θ t + s * L.Θ 0)
      ((1 - s) * L.Φ t + s * L.Φ 0), ?_, ?_, ?_, ?_, ?_⟩
  · show Continuous (fun p : ℝ × ℝ => P.psi ((1 - p.1) * L.Θ p.2 + p.1 * L.Θ 0)
        ((1 - p.1) * L.Φ p.2 + p.1 * L.Φ 0))
    have hc : Continuous (Function.uncurry P.psi) := P.cont
    exact hc.comp (Continuous.prodMk
      (((continuous_const.sub continuous_fst).mul (L.contΘ.comp continuous_snd)).add
        (continuous_fst.mul continuous_const))
      (((continuous_const.sub continuous_fst).mul (L.contΦ.comp continuous_snd)).add
        (continuous_fst.mul continuous_const)))
  · intro s t; exact P.psi_mem_carrier _ _
  · intro t
    simp only [sub_zero, one_mul, zero_mul, add_zero]
    exact L.lifts t
  · intro t
    simp only [sub_self, zero_mul, one_mul, zero_add]
    rfl
  · intro s t
    obtain ⟨h1, h2⟩ := hper t
    show P.psi ((1 - s) * L.Θ (t + 2 * Real.pi) + s * L.Θ 0)
        ((1 - s) * L.Φ (t + 2 * Real.pi) + s * L.Φ 0)
      = P.psi ((1 - s) * L.Θ t + s * L.Θ 0) ((1 - s) * L.Φ t + s * L.Φ 0)
    rw [h1, h2]

theorem not_isEssential_iff_homotopic_const (P : Work.CoreTopology.ParamTorus)
    (γ : Work.CoreTopology.ClosedCurve P) :
    ¬ Work.CoreTopology.IsEssential P γ ↔
      ∃ (x : LeanEval.KnotTheory.PardonDistortion.R3) (hx : x ∈ P.carrier),
        Work.CoreTopology.Homotopic P γ (Work.InnermostDisk.constCurve P x hx) := by
  constructor
  · intro h
    obtain ⟨L⟩ := Work.TorusCover.ParamTorus_exists_liftOf P γ
    have hw : L.winding = (0, 0) := by
      by_contra hne
      exact h ⟨L, hne⟩
    exact homotopic_const_of_winding_eq_zero L hw
  · rintro ⟨x, hx, hhom⟩ hess
    exact not_isEssential_of_const P x hx (isEssential_iff_of_homotopic hhom |>.mp hess)

end

end Work.InnermostDisk
