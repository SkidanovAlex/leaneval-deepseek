import Mathlib
import Submission.Work.Drive.cappedPlaneDisjoint
import Submission.Work.Drive.stripConfigInterface

/-!
# The cone parametrisation of the cap disk

`Work.Drive.capCone r₀ ρ Ψ Θ u` is the cap disk of the capped plane
`Work.Drive.cappedPlane r₀ ρ Ψ Θ μ u` of the configuration Möbius strip: the cone with apex
`(r₀, Θ 0 + u, 0)` over the boundary curve `t ↦ (ρ t, Θ t + u, circleOf (Ψ t))` of the cap solid
torus.  This file fixes the **parametrisation** of that cone

> `Work.Drive.capConePt r₀ ρ Ψ Θ u s t = ((1 - s) * r₀ + s * ρ t, Θ 0 + s * (Θ t - Θ 0) + u,
>     s • circleOf (Ψ t))`

(as a point of `ℝ × ℝ/ℤ × ℂ`), records its elementary properties — positivity, the norm `‖s‖` of the
disk coordinate, the `2π`-periodicity in `t`, the collapse of the apex `s = 0` — and identifies its two
faces in the capping space:

* at `s = 1` the parametrisation is the *boundary* of the cap disk, and its class in
  `Work.Drive.CappingSpace` is the class of the **diagonal point of the configuration strip** at
  `Circle.exp t`, rotated by `u` (`Work.Drive.mk_capConePt_one_eq_rot_diag`): this is the gluing
  `∂cap = ∂M`;
* at `s = 0` it is the apex of the cone, independent of `t`.

This is the "cap half" of the disk presentation of `P_u` (see `ESSENTIAL_LOOP_CORRECTION.md` and
`SWEEP_TRANSPORT_NOTES.md` §3–§4): the map `z ↦ capConePt r₀ ρ Ψ Θ u (2‖z‖) t(z)` on the disk
`‖z‖ ≤ 1/2`, with `t(z)` the parameter of the direction `z/‖z‖`, is the parametrisation of the cap
half of the disk model of `P_u ≅ ℝP²`.
-/

set_option autoImplicit false
noncomputable section

namespace Work.Drive

open scoped Topology

/-! ## The parametrisation and its elementary properties -/

/-- **The cone parametrisation of the cap disk.**  The point of `ℝ × ℝ/ℤ × ℂ` on the cone from the
apex `(r₀, Θ 0 + u, 0)` to the boundary curve `t ↦ (ρ t, Θ t + u, circleOf (Ψ t))` at parameter
`s ∈ [0,1]`. -/
def capConePt (r₀ : ℝ) (ρ Ψ Θ : ℝ → ℝ) (u : UnitAddCircle) (s t : ℝ) :
    ℝ × UnitAddCircle × ℂ :=
  ((1 - s) * r₀ + s * ρ t, (((Θ 0 + s * (Θ t - Θ 0) : ℝ)) : UnitAddCircle) + u,
    (s : ℂ) * circleOf ((Ψ t : ℝ) : UnitAddCircle))

@[simp] lemma capConePt_fst (r₀ : ℝ) (ρ Ψ Θ : ℝ → ℝ) (u : UnitAddCircle) (s t : ℝ) :
    (capConePt r₀ ρ Ψ Θ u s t).1 = (1 - s) * r₀ + s * ρ t := rfl

@[simp] lemma capConePt_snd (r₀ : ℝ) (ρ Ψ Θ : ℝ → ℝ) (u : UnitAddCircle) (s t : ℝ) :
    (capConePt r₀ ρ Ψ Θ u s t).2.1 =
      (((Θ 0 + s * (Θ t - Θ 0) : ℝ)) : UnitAddCircle) + u := rfl

@[simp] lemma capConePt_thd (r₀ : ℝ) (ρ Ψ Θ : ℝ → ℝ) (u : UnitAddCircle) (s t : ℝ) :
    (capConePt r₀ ρ Ψ Θ u s t).2.2 = (s : ℂ) * circleOf ((Ψ t : ℝ) : UnitAddCircle) := rfl

/-- **The radial coordinate of a cone point is positive.**  It is a convex combination of the two
positive numbers `r₀` (the apex radius) and `ρ t` (the radius of the boundary curve). -/
lemma capConePt_pos {r₀ : ℝ} {ρ : ℝ → ℝ} (hr₀ : 0 < r₀) (hρ : ∀ t : ℝ, 0 < ρ t)
    (Ψ Θ : ℝ → ℝ) (u : UnitAddCircle) {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    0 < (capConePt r₀ ρ Ψ Θ u s t).1 := by
  have hs0 : 0 ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  rw [capConePt_fst]
  rcases eq_or_lt_of_le hs0 with hzero | hpos
  · subst hzero
    simp only [zero_mul, sub_zero, one_mul, add_zero]
    exact hr₀
  · have h2 : 0 < s * ρ t := mul_pos hpos (hρ t)
    have h1 : 0 ≤ (1 - s) * r₀ := mul_nonneg (by linarith) hr₀.le
    linarith

/-- The disk coordinate of a cone point has norm `|s|`. -/
lemma capConePt_thd_norm (r₀ : ℝ) (ρ Ψ Θ : ℝ → ℝ) (u : UnitAddCircle) (s t : ℝ) :
    ‖(capConePt r₀ ρ Ψ Θ u s t).2.2‖ = |s| := by
  simp only [capConePt_thd, norm_mul, norm_circleOf, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- The disk coordinate of a cone point of parameter `s ∈ [0,1]` lies in the disk. -/
lemma capConePt_thd_norm_le_one (r₀ : ℝ) (ρ Ψ Θ : ℝ → ℝ) (u : UnitAddCircle) {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) : ‖(capConePt r₀ ρ Ψ Θ u s t).2.2‖ ≤ 1 := by
  rw [capConePt_thd_norm, abs_of_nonneg hs.1]
  exact hs.2

/-- **A cone point with parameter in `[0,1]` is a point of the cap cone.** -/
lemma capConePt_mem_capCone {r₀ : ℝ} {ρ : ℝ → ℝ} (hr₀ : 0 < r₀) (hρ : ∀ t : ℝ, 0 < ρ t)
    (Ψ Θ : ℝ → ℝ) (u : UnitAddCircle) {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (⟨capConePt r₀ ρ Ψ Θ u s t, capConePt_pos hr₀ hρ Ψ Θ u hs, capConePt_thd_norm_le_one r₀ ρ Ψ Θ u hs⟩ :
        CapPiece) ∈ capCone r₀ ρ Ψ Θ u :=
  ⟨s, t, hs, rfl⟩

/-! ## Periodicity in the parameter and the apex -/

/-- **The cone parametrisation is `2π`-periodic in `t`.** -/
lemma capConePt_periodic {r₀ : ℝ} {ρ Ψ Θ : ℝ → ℝ} (hρ : ∀ t : ℝ, ρ (t + 2 * Real.pi) = ρ t)
    (hΨ : ∀ t : ℝ, circleOf ((Ψ (t + 2 * Real.pi) : ℝ) : UnitAddCircle) =
      circleOf ((Ψ t : ℝ) : UnitAddCircle))
    (hΘ : ∀ t : ℝ, Θ (t + 2 * Real.pi) = Θ t) (u : UnitAddCircle) (s t : ℝ) :
    capConePt r₀ ρ Ψ Θ u s (t + 2 * Real.pi) = capConePt r₀ ρ Ψ Θ u s t := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [capConePt_fst]
    rw [hρ t]
  · simp only [capConePt_snd]
    rw [hΘ t]
  · simp only [capConePt_thd]
    rw [hΨ t]

/-- **The cone point of parameter `s = 0` is the apex** `(r₀, Θ 0 + u, 0)`, independently of the
angular parameter. -/
lemma capConePt_zero (r₀ : ℝ) (ρ Ψ Θ : ℝ → ℝ) (u : UnitAddCircle) (t : ℝ) :
    capConePt r₀ ρ Ψ Θ u 0 t = (r₀, (((Θ 0 : ℝ)) : UnitAddCircle) + u, 0) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [capConePt_fst]
    norm_num
  · simp only [capConePt_snd]
    norm_num
  · simp only [capConePt_thd]
    norm_num

/-- **The cone point of parameter `s = 0` is the apex** (any two angular parameters agree). -/
lemma capConePt_zero_eq (r₀ : ℝ) (ρ Ψ Θ : ℝ → ℝ) (u : UnitAddCircle) (t t' : ℝ) :
    capConePt r₀ ρ Ψ Θ u 0 t = capConePt r₀ ρ Ψ Θ u 0 t' :=
  (capConePt_zero r₀ ρ Ψ Θ u t).trans (capConePt_zero r₀ ρ Ψ Θ u t').symm

/-- The coordinates of the cone point at `s = 1`: the boundary circle of the cap disk. -/
@[simp] lemma capConePt_one_fst (r₀ : ℝ) (ρ Ψ Θ : ℝ → ℝ) (u : UnitAddCircle) (t : ℝ) :
    (capConePt r₀ ρ Ψ Θ u 1 t).1 = ρ t := by
  simp only [capConePt_fst]; ring

@[simp] lemma capConePt_one_snd (r₀ : ℝ) (ρ Ψ Θ : ℝ → ℝ) (u : UnitAddCircle) (t : ℝ) :
    (capConePt r₀ ρ Ψ Θ u 1 t).2.1 = ((Θ t : ℝ) : UnitAddCircle) + u := by
  simp only [capConePt_snd]
  norm_num

@[simp] lemma capConePt_one_thd (r₀ : ℝ) (ρ Ψ Θ : ℝ → ℝ) (u : UnitAddCircle) (t : ℝ) :
    (capConePt r₀ ρ Ψ Θ u 1 t).2.2 = circleOf ((Ψ t : ℝ) : UnitAddCircle) := by
  simp only [capConePt_thd]
  norm_num

/-- **The `s = 1` face of the cone is the boundary circle of the cap disk** (`capBdy`). -/
lemma capConePt_one_eq_capBdy {r₀ : ℝ} {ρ Ψ Θ : ℝ → ℝ} {u : UnitAddCircle} {t : ℝ}
    (hρ : 0 < ρ t) :
    capConePt r₀ ρ Ψ Θ u 1 t = (capBdy (ρ t) hρ (((Θ t : ℝ) : UnitAddCircle) + u)
      (((Ψ t : ℝ) : UnitAddCircle))) := by
  refine Prod.ext (capConePt_one_fst r₀ ρ Ψ Θ u t) ?_
  refine Prod.ext (capConePt_one_snd r₀ ρ Ψ Θ u t) ?_
  rw [capConePt_one_thd]
  rfl

section Gluing

variable {γ : Circle → ℝ × ℝ} {ρ Ψ Θ : ℝ → ℝ} {r₀ : ℝ} {u : UnitAddCircle}

/-- **The `s = 1` face of the cap cone is the diagonal point of the configuration strip.**  For a
smooth Jordan curve `γ` with `0 ∉ γ`, polar data `polarLift (ρ t, Ψ t) = γ (Circle.exp t)` and a cap
angle `Θ` with `Θ t = tangentDirC γ (Circle.exp t) - 2 Ψ t`, the class in the capping space of the
cap boundary point at parameter `t` (rotated by `u`) is the class of the diagonal configuration point
`(γ (Circle.exp t), tangentDirC γ (Circle.exp t), 0)` of the strip.  This is the gluing
`∂cap = ∂M` of the capped plane `P_u = u·M ∪ cap_u`. -/
theorem mk_capConePt_one_eq_rot_diag (hr₀ : 0 < r₀) (hρ : ∀ t : ℝ, 0 < ρ t)
    (hpolar : ∀ t : ℝ, polarLift (ρ t, Ψ t) = γ (Circle.exp t))
    (hΘclass : ∀ t : ℝ, ((Θ t : ℝ) : UnitAddCircle)
      = tangentDirC γ (Circle.exp t) - 2 • ((Ψ t : ℝ) : UnitAddCircle))
    (t : ℝ)
    (h1 : 0 < (confOf (γ (Circle.exp t), tangentDirC γ (Circle.exp t), 0)).1)
    (h2 : ‖(confOf (γ (Circle.exp t), tangentDirC γ (Circle.exp t), 0)).2.1‖ ≤ 1) :
    (Quotient.mk'' (Sum.inr (⟨capConePt r₀ ρ Ψ Θ u 1 t,
        capConePt_pos hr₀ hρ Ψ Θ u (by constructor <;> norm_num),
        capConePt_thd_norm_le_one r₀ ρ Ψ Θ u (by constructor <;> norm_num)⟩ : CapPiece)
        : ConfigPiece ⊕ CapPiece) : CappingSpace)
      = rotCapping u (Quotient.mk'' (Sum.inl (confPiece
          (γ (Circle.exp t), tangentDirC γ (Circle.exp t), 0) h1 h2)
            : ConfigPiece ⊕ CapPiece) : CappingSpace) := by
  set P : CapPiece := ⟨capConePt r₀ ρ Ψ Θ u 1 t,
    capConePt_pos hr₀ hρ Ψ Θ u (by constructor <;> norm_num),
    capConePt_thd_norm_le_one r₀ ρ Ψ Θ u (by constructor <;> norm_num)⟩ with hP
  set Q : ConfigPiece := confPiece (γ (Circle.exp t), tangentDirC γ (Circle.exp t), 0) h1 h2 with hQ
  -- the value of `P` is that of the cap boundary point with cap angle `Θ t + u`
  have hPval : (P : ℝ × UnitAddCircle × ℂ)
      = (capBdy (ρ t) (hρ t) (((Θ t : ℝ) : UnitAddCircle) + u)
          (((Ψ t : ℝ) : UnitAddCircle)) : ℝ × UnitAddCircle × ℂ) := by
    rw [hP]
    simp only [capBdy_val]
    exact Prod.ext (capConePt_one_fst r₀ ρ Ψ Θ u t)
      (Prod.ext (capConePt_one_snd r₀ ρ Ψ Θ u t) (capConePt_one_thd r₀ ρ Ψ Θ u t))
  -- the value of `Q` is that of the configuration boundary point with angle `Ψ t`
  have hQval : (Q : ℝ × ℂ × UnitAddCircle)
      = (confBdy (ρ t) (hρ t) (((Ψ t : ℝ) : UnitAddCircle))
          (tangentDirC γ (Circle.exp t)) : ℝ × ℂ × UnitAddCircle) := by
    rw [hQ]
    rw [confPiece_val, confBdy_val]
    exact confOf_eq_of_polarLift (hρ t) (hpolar t) (tangentDirC γ (Circle.exp t))
  have hPsub : P = capBdy (ρ t) (hρ t) (((Θ t : ℝ) : UnitAddCircle) + u)
      (((Ψ t : ℝ) : UnitAddCircle)) := Subtype.ext hPval
  have hQsub : Q = confBdy (ρ t) (hρ t) (((Ψ t : ℝ) : UnitAddCircle))
      (tangentDirC γ (Circle.exp t)) := Subtype.ext hQval
  -- the angle relation: the doubled tangent direction is `Θ t + 2 Ψ t`
  have hη : tangentDirC γ (Circle.exp t)
      = ((Θ t : ℝ) : UnitAddCircle) + 2 • ((Ψ t : ℝ) : UnitAddCircle) :=
    eq_add_of_sub_eq (hΘclass t).symm
  have hglue : (Quotient.mk'' (Sum.inr (capBdy (ρ t) (hρ t)
        (((Θ t : ℝ) : UnitAddCircle)) (((Ψ t : ℝ) : UnitAddCircle)))
          : ConfigPiece ⊕ CapPiece) : CappingSpace)
      = Quotient.mk'' (Sum.inl (confBdy (ρ t) (hρ t)
          (((Ψ t : ℝ) : UnitAddCircle)) (tangentDirC γ (Circle.exp t)))
            : ConfigPiece ⊕ CapPiece) := by
    rw [hη]
    exact (mk_confBdy_eq_mk_capBdy (ρ t) (hρ t) (((Θ t : ℝ) : UnitAddCircle))
      (((Ψ t : ℝ) : UnitAddCircle))).symm
  calc (Quotient.mk'' (Sum.inr P) : CappingSpace)
      = Quotient.mk'' (Sum.inr (capBdy (ρ t) (hρ t)
          (((Θ t : ℝ) : UnitAddCircle) + u) (((Ψ t : ℝ) : UnitAddCircle))) :
            ConfigPiece ⊕ CapPiece) := by rw [hPsub]
    _ = rotCapping u (Quotient.mk'' (Sum.inr (capBdy (ρ t) (hρ t)
          (((Θ t : ℝ) : UnitAddCircle)) (((Ψ t : ℝ) : UnitAddCircle))) :
            ConfigPiece ⊕ CapPiece)) := by
        rw [rotCapping_mk, rotSum_inr]
        rfl
    _ = rotCapping u (Quotient.mk'' (Sum.inl (confBdy (ρ t) (hρ t)
          (((Ψ t : ℝ) : UnitAddCircle)) (tangentDirC γ (Circle.exp t))) :
            ConfigPiece ⊕ CapPiece)) := by rw [hglue]
    _ = rotCapping u (Quotient.mk'' (Sum.inl Q) : CappingSpace) := by rw [hQsub]

end Gluing

end Work.Drive
