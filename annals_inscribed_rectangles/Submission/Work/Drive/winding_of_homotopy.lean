import Mathlib
import Submission.Work.Drive.WindingNumber
import Submission.Work.Drive.degree_homotopic

namespace Work.Drive

/-! `Work.Drive.winding γ hγ hp` is the degree of the direction map `t ↦ dirC (γ t - p)`.  If `γ` is
deformed by a continuous homotopy `H` that never passes through the point `p`, the direction maps
form a homotopy of circle maps and the degree does not change (`Work.Drive.degree_homotopic`).

This is the isotopy invariance used by Hugelmeyer's capping: the position coordinate of `∂M` is the
degree of `γ` about the origin, and the capping only uses the isotopy class of `∂M` (the boundary is
isotopic to `T(2,1) × {0}`). -/



/-- **The direction map of a homotopy of curves avoiding `p`.**

If `Φ : I × ℝ/ℤ → ℝ²` never hits `p`, then `x ↦ dirC (Φ x - p)` is a continuous circle map, and it
interpolates between the direction maps of the two end curves `t ↦ Φ (0, t)` and `t ↦ Φ (1, t)`. -/
noncomputable def homotopyDir (Φ : C(unitInterval × UnitAddCircle, ℝ × ℝ)) (p : ℝ × ℝ)
    (hp : ∀ s : unitInterval, p ∉ Set.range (fun t : UnitAddCircle => Φ (s, t))) :
    C(unitInterval × UnitAddCircle, UnitAddCircle) where
  toFun x := Submission.Collision.dirC (Φ x - p)
  continuous_toFun := by
    have hne : ∀ x : unitInterval × UnitAddCircle, Φ x - p ≠ 0 := by
      rintro ⟨s, t⟩ h
      exact hp s ⟨t, sub_eq_zero.mp h⟩
    have hcont : Continuous (fun x : unitInterval × UnitAddCircle => Φ x - p) :=
      Φ.continuous.sub continuous_const
    have hcomp : ContinuousOn (Submission.Collision.dirC ∘ fun x => Φ x - p) Set.univ :=
      Submission.Configuration.continuousOn_dirC.comp hcont.continuousOn
        (fun x _ => hne x)
    exact continuousOn_univ.mp hcomp

lemma homotopyDir_apply_zero (Φ : C(unitInterval × UnitAddCircle, ℝ × ℝ)) (p : ℝ × ℝ)
    (hp : ∀ s : unitInterval, p ∉ Set.range (fun t : UnitAddCircle => Φ (s, t)))
    (h₀ : Continuous (fun t : UnitAddCircle => Φ (0, t))) (t : UnitAddCircle) :
    homotopyDir Φ p hp (0, t) = dirCurve (fun t : UnitAddCircle => Φ (0, t)) h₀ p (hp 0) t :=
  rfl

lemma homotopyDir_apply_one (Φ : C(unitInterval × UnitAddCircle, ℝ × ℝ)) (p : ℝ × ℝ)
    (hp : ∀ s : unitInterval, p ∉ Set.range (fun t : UnitAddCircle => Φ (s, t)))
    (h₁ : Continuous (fun t : UnitAddCircle => Φ (1, t))) (t : UnitAddCircle) :
    homotopyDir Φ p hp (1, t) = dirCurve (fun t : UnitAddCircle => Φ (1, t)) h₁ p (hp 1) t :=
  rfl

/-- **Homotopy invariance of the winding number about a fixed point.**

The direction maps of the two end curves are homotopic circle maps (through the direction maps of
the intermediate curves), so their degrees agree by `Work.Drive.degree_homotopic`.

The two continuity proofs are explicit arguments to make the statement usable without any
definitional bookkeeping about how they were obtained. -/
theorem winding_of_homotopy_aux {Φ : C(unitInterval × UnitAddCircle, ℝ × ℝ)} {p : ℝ × ℝ}
    (hp : ∀ s : unitInterval, p ∉ Set.range (fun t : UnitAddCircle => Φ (s, t)))
    (h₀ : Continuous (fun t : UnitAddCircle => Φ (0, t)))
    (h₁ : Continuous (fun t : UnitAddCircle => Φ (1, t))) :
    winding (fun t : UnitAddCircle => Φ (0, t)) h₀ (hp 0) =
      winding (fun t : UnitAddCircle => Φ (1, t)) h₁ (hp 1) := by
  have hhom : (⟨dirCurve (fun t : UnitAddCircle => Φ (0, t)) h₀ p (hp 0),
        continuous_dirCurve _ h₀ p (hp 0)⟩ : C(UnitAddCircle, UnitAddCircle)).Homotopic
      ⟨dirCurve (fun t : UnitAddCircle => Φ (1, t)) h₁ p (hp 1),
        continuous_dirCurve _ h₁ p (hp 1)⟩ :=
    ⟨ContinuousMap.Homotopy.mk (homotopyDir Φ p hp)
      (homotopyDir_apply_zero Φ p hp h₀) (homotopyDir_apply_one Φ p hp h₁)⟩
  show winding (fun t : UnitAddCircle => Φ (0, t)) h₀ (hp 0) =
    winding (fun t : UnitAddCircle => Φ (1, t)) h₁ (hp 1)
  rw [winding, winding]
  exact degree_homotopic hhom

theorem winding_of_homotopy {H : C(unitInterval × UnitAddCircle, ℝ × ℝ)} {p : ℝ × ℝ}
    (hp : ∀ s : unitInterval, p ∉ Set.range (fun t : UnitAddCircle => H (s, t))) :
    Work.Drive.winding (fun t : UnitAddCircle => H (0, t)) (by fun_prop) (hp 0) =
      Work.Drive.winding (fun t : UnitAddCircle => H (1, t)) (by fun_prop) (hp 1) :=
  winding_of_homotopy_aux (Φ := H) hp _ _

end Work.Drive
