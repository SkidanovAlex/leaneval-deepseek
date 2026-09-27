import Mathlib
import Submission.Work.Drive.capConeDefs
import Submission.Work.Drive.circOf_half_sq
import Submission.Work.Drive.contMDiffAt_cappingSpace_capPieceClass
import Submission.Work.Drive.contDiffOn_chordUnitDir

/-!
# The cone chart of the cap disk is smooth on the interior

This file proves `Work.Drive.contMDiffOn_capConeChart`: the clamped cone chart
`Work.Drive.capConeChart` of the cap disk of the capping space (`capConeDefs.lean`) is `C^∞` for the
transparent smooth structure `Work.Drive.cappingCharted`, on the open set
`{p | 0 < p 0 ∧ p 0 < 1}` (the *interior* of the cone square `[0,1] × S¹`).

The only content beyond polynomial algebra is the **sphere lift** of the cone's `S¹`-coordinate: the
cap coordinate of the cone point is the class of `Θ 0 + s (Θ t - Θ 0)`, whose smooth square root is
`w₀ · circleOf (s (Θ t - Θ 0) / 2)` with a *constant* `w₀` satisfying `w₀ ^ 2 = circleOf (Θ 0 + u)`
(the proved `Work.Drive.circOf_half_sq`); the square root has to be carried as data because the class
`Θ 0 + u` has no continuous square root (`Submission/Work/Drive/CAPPING_ANALYSIS.md` §2).
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology
open Classical

noncomputable section

/-- **The parametrisation of the circle by real classes is smooth in the class.**  Via
`Work.Drive.circleOf_coe_eq_exp` this is the smoothness of `t ↦ exp (2π i t)`. -/
lemma contDiff_circleOf_coe :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => circleOf ((t : ℝ) : UnitAddCircle)) := by
  have h : (fun t : ℝ => circleOf ((t : ℝ) : UnitAddCircle))
      = fun t : ℝ => Complex.exp (((2 * Real.pi * t : ℝ)) * Complex.I) := by
    funext t
    exact circleOf_coe_eq_exp t
  rw [h]
  have hlin : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => (((2 * Real.pi * t : ℝ)) : ℂ) * Complex.I) :=
    (Complex.ofRealCLM.contDiff.comp
      (by fun_prop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t : ℝ => (2 * Real.pi * t : ℝ)))).mul contDiff_const
  exact Complex.contDiff_exp.comp hlin

/-- The clamp of the cone parameter is smooth on the interior `(0,1)` of the square (where it is the
identity). -/
lemma contDiffOn_capConeClamp : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) capConeClamp (Set.Ioo (0:ℝ) 1) :=
  contDiff_id.contDiffOn.congr (fun _s hs => capConeClamp_of_mem ⟨hs.1.le, hs.2.le⟩)

/-- The cone chart of the cap disk, in the normal form of
`Work.Drive.contMDiffAt_cappingSpace_capPieceClass`, equals `Work.Drive.capConeChart`. -/
lemma capConeChart_eq_piece (r₀ : ℝ) (ρ Ψ Θ : ℝ → ℝ) (u : UnitAddCircle) (hr₀ : 0 < r₀)
    (hρpos : ∀ t : ℝ, 0 < ρ t) {w₀ : ℂ}
    (hw₀ : w₀ ^ 2 = circleOf ((((Θ 0 : ℝ)) : UnitAddCircle) + u)) (hw₀1 : ‖w₀‖ = 1)
    (p : EuclideanSpace ℝ (Fin 2)) :
    capConeChart r₀ ρ Ψ Θ u hr₀ hρpos p =
      Quotient.mk'' (Sum.inr (⟨((capConePt r₀ ρ Ψ Θ u (capConeClamp (p 0)) (p 1)).1,
        circOf ((w₀ * circleOf ((((capConeClamp (p 0) * (Θ (p 1) - Θ 0) / 2 : ℝ)) : UnitAddCircle))) ^ 2)
          (by rw [norm_pow, norm_mul, hw₀1, norm_circleOf, mul_one, one_pow]),
        (capConePt r₀ ρ Ψ Θ u (capConeClamp (p 0)) (p 1)).2.2),
        capConePt_pos hr₀ hρpos Ψ Θ u (capConeClamp_mem (p 0)),
        capConePt_thd_norm_le_one r₀ ρ Ψ Θ u (capConeClamp_mem (p 0))⟩ : CapPiece)) := by
  refine Quotient.sound (Or.inl (congrArg Sum.inr (Subtype.ext ?_)))
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  rw [capConePt_snd]
  exact (circOf_half_sq (Θ 0) u hw₀ hw₀1 (capConeClamp (p 0)) (Θ (p 1) - Θ 0)).symm

/-- **The cone chart of the cap disk is `C^∞` on the interior of the cone square.** -/
theorem contMDiffOn_capConeChart (r₀ : ℝ) (ρ Ψ Θ : ℝ → ℝ) (u : UnitAddCircle) (hr₀ : 0 < r₀)
    (hρpos : ∀ t : ℝ, 0 < ρ t)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (hΘ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ)
    {w₀ : ℂ} (hw₀ : w₀ ^ 2 = circleOf ((((Θ 0 : ℝ)) : UnitAddCircle) + u)) (hw₀1 : ‖w₀‖ = 1) :
    letI := cappingCharted
    ContMDiffOn (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (capConeChart r₀ ρ Ψ Θ u hr₀ hρpos)
      {p : EuclideanSpace ℝ (Fin 2) | 0 < p 0 ∧ p 0 < 1} := by
  letI := cappingCharted
  intro p₀ hp₀
  -- the clamped cone parameter is smooth at an interior point
  have hclamp : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) capConeClamp (p₀ 0) :=
    contDiffOn_capConeClamp.contDiffAt (isOpen_Ioo.mem_nhds ⟨hp₀.1, hp₀.2⟩)
  have hproj : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 2) => p 0) p₀ := by fun_prop
  have hσ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 2) => capConeClamp (p 0)) p₀ :=
    ContDiffAt.comp (g := capConeClamp) p₀ hclamp hproj
  -- the three data functions
  have hρc : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 2) => ρ (p 1)) p₀ :=
    hρ.contDiffAt.comp p₀ (by fun_prop)
  have hΘc : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 2) => Θ (p 1) - Θ 0) p₀ :=
    (hΘ.contDiffAt.comp p₀ (by fun_prop)).sub contDiffAt_const
  have hΨr : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 2) => Ψ (p 1)) p₀ :=
    hΨ.contDiffAt.comp p₀ (by fun_prop)
  have hΨc : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 2) => circleOf (((Ψ (p 1) : ℝ)) : UnitAddCircle)) p₀ :=
    contDiff_circleOf_coe.contDiffAt.comp p₀ hΨr
  have harg : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 2) => ((capConeClamp (p 0) * (Θ (p 1) - Θ 0) / 2 : ℝ))) p₀ :=
    (hσ.mul hΘc).div_const 2
  have hcirc : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 2) =>
        circleOf ((((capConeClamp (p 0) * (Θ (p 1) - Θ 0) / 2 : ℝ)) : UnitAddCircle))) p₀ :=
    contDiff_circleOf_coe.contDiffAt.comp p₀ harg
  have hRcd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 2) => (capConePt r₀ ρ Ψ Θ u (capConeClamp (p 0)) (p 1)).1) p₀ := by
    have h : (fun p : EuclideanSpace ℝ (Fin 2) =>
        (capConePt r₀ ρ Ψ Θ u (capConeClamp (p 0)) (p 1)).1)
        = fun p : EuclideanSpace ℝ (Fin 2) => (1 - capConeClamp (p 0)) * r₀ + capConeClamp (p 0) * ρ (p 1) :=
      funext (fun p => capConePt_fst r₀ ρ Ψ Θ u (capConeClamp (p 0)) (p 1))
    rw [h]
    exact (((contDiffAt_const.sub hσ).mul contDiffAt_const).add (hσ.mul hρc))
  have hDcd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 2) => (capConePt r₀ ρ Ψ Θ u (capConeClamp (p 0)) (p 1)).2.2) p₀ := by
    have h : (fun p : EuclideanSpace ℝ (Fin 2) =>
        (capConePt r₀ ρ Ψ Θ u (capConeClamp (p 0)) (p 1)).2.2)
        = fun p : EuclideanSpace ℝ (Fin 2) =>
            ((capConeClamp (p 0) : ℝ) : ℂ) * circleOf (((Ψ (p 1) : ℝ)) : UnitAddCircle) :=
      funext (fun p => capConePt_thd r₀ ρ Ψ Θ u (capConeClamp (p 0)) (p 1))
    rw [h]
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp p₀ hσ).mul hΨc
  have hZcd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 2) =>
        w₀ * circleOf ((((capConeClamp (p 0) * (Θ (p 1) - Θ 0) / 2 : ℝ)) : UnitAddCircle))) p₀ :=
    contDiffAt_const.mul hcirc
  -- the three data functions as `ContMDiffAt`
  have hR : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 2) => (capConePt r₀ ρ Ψ Θ u (capConeClamp (p 0)) (p 1)).1) p₀ :=
    contMDiffAt_iff_contDiffAt.mpr hRcd
  have hD : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 2) => (capConePt r₀ ρ Ψ Θ u (capConeClamp (p 0)) (p 1)).2.2) p₀ :=
    contMDiffAt_iff_contDiffAt.mpr hDcd
  have hZ : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 2) =>
        w₀ * circleOf ((((capConeClamp (p 0) * (Θ (p 1) - Θ 0) / 2 : ℝ)) : UnitAddCircle))) p₀ :=
    contMDiffAt_iff_contDiffAt.mpr hZcd
  -- the piece lemma
  have hpiece := contMDiffAt_cappingSpace_capPieceClass (k := 2)
    (fun p : EuclideanSpace ℝ (Fin 2) => (capConePt r₀ ρ Ψ Θ u (capConeClamp (p 0)) (p 1)).1)
    (fun p => w₀ * circleOf ((((capConeClamp (p 0) * (Θ (p 1) - Θ 0) / 2 : ℝ)) : UnitAddCircle)))
    (fun p => (capConePt r₀ ρ Ψ Θ u (capConeClamp (p 0)) (p 1)).2.2) p₀
    (fun p => capConePt_pos hr₀ hρpos Ψ Θ u (capConeClamp_mem (p 0)))
    (fun p => capConePt_thd_norm_le_one r₀ ρ Ψ Θ u (capConeClamp_mem (p 0)))
    (fun p => by rw [norm_mul, hw₀1, norm_circleOf, mul_one])
    hR hZ hD
  refine (hpiece.contMDiffWithinAt).congr_of_eventuallyEq ?_ ?_
  · exact Filter.EventuallyEq.of_eq
      (funext (fun p => (capConeChart_eq_piece r₀ ρ Ψ Θ u hr₀ hρpos hw₀ hw₀1 p)))
  · exact capConeChart_eq_piece r₀ ρ Ψ Θ u hr₀ hρpos hw₀ hw₀1 p₀

end

end Work.Drive
