import Mathlib
import Submission.Work.Conn.Basic

/-!
# Extending a null-homotopic map on the sphere over the ball

This file proves `Work.Conn.Extend.exists_continuousMap_ball_of_homotopic_const`: a map
`g : 𝕊ᵐ → Y` that is homotopic to a constant map extends continuously over the closed ball
`𝔻ᵐ⁺¹`.  The null-homotopy is a map on the cone on `𝕊ᵐ`, and the cone on `𝕊ᵐ` is the ball,
realised concretely by "radius = time".

## Main results

* `Work.Conn.Extend.exists_continuousMap_ball_of_homotopic_const`
-/

open ContinuousMap

namespace Work.Conn.Extend

noncomputable section

/-- The time coordinate of the cone parametrisation of the ball: the point `p` is sent to the
cone height `min (2 * (1 - ‖p‖)) 1`, clamped into `[0,1]`.  On the unit sphere this is `0`, and on
the ball of radius `1/2` it is `1`. -/
def coneTime {m : ℕ} (p : EuclideanSpace ℝ (Fin (m + 1))) : unitInterval :=
  ⟨max 0 (min (2 * (1 - ‖p‖)) 1),
    ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩⟩

@[simp] theorem coe_coneTime {m : ℕ} (p : EuclideanSpace ℝ (Fin (m + 1))) :
    ((coneTime p : unitInterval) : ℝ) = max 0 (min (2 * (1 - ‖p‖)) 1) := rfl

theorem continuous_coneTime {m : ℕ} : Continuous (coneTime (m := m)) := by
  unfold coneTime; fun_prop

/-- The cone time is `1` on the ball of radius `1/2`. -/
theorem coneTime_eq_one_of_norm_le {m : ℕ} {p : EuclideanSpace ℝ (Fin (m+1))}
    (h : ‖p‖ ≤ (1:ℝ)/2) : coneTime p = 1 := by
  apply Subtype.ext
  rw [coe_coneTime]
  have h2 : (1:ℝ) ≤ 2 * (1 - ‖p‖) := by linarith
  rw [min_eq_right h2, max_eq_right zero_le_one]
  rfl

/-- The cone time is `0` on the unit sphere. -/
theorem coneTime_eq_zero_of_norm_eq_one {m : ℕ} {p : EuclideanSpace ℝ (Fin (m+1))}
    (h : ‖p‖ = 1) : coneTime p = 0 := by
  apply Subtype.ext
  rw [coe_coneTime, h]
  norm_num

/-- The raw conical map: the value of the homotopy `Φc` at the radial projection of `p` and the
cone time.  The value at the origin is irrelevant (it is never used) and is set to `y₀`. -/
def coneMap {m : ℕ} {Y : Type*} [TopologicalSpace Y]
    (Φc : C(unitInterval × Sph m, Y)) (y₀ : Y) (p : Ball (m + 1)) : Y :=
  if hp : (p : EuclideanSpace ℝ (Fin (m + 1))) = 0 then y₀
  else Φc (coneTime (p : EuclideanSpace ℝ (Fin (m + 1))),
    ⟨‖(p : EuclideanSpace ℝ (Fin (m + 1)))‖⁻¹ • (p : EuclideanSpace ℝ (Fin (m + 1))),
      mem_Sph_iff.mpr (norm_inv_norm_smul hp)⟩)

/-- The map on the whole ball: for `‖p‖ ≥ 1/2` use the conical map, for `‖p‖ ≤ 1/2` use the
constant `y₀`.  On the overlap `‖p‖ = 1/2` both agree, since the cone time is `1` there. -/
def ballConeMap {m : ℕ} {Y : Type*} [TopologicalSpace Y]
    (Φc : C(unitInterval × Sph m, Y)) (y₀ : Y) (p : Ball (m + 1)) : Y :=
  if (1:ℝ)/2 ≤ ‖(p : EuclideanSpace ℝ (Fin (m + 1)))‖ then coneMap Φc y₀ p else y₀

/-- `coneMap` is continuous on the closed half-ball `{‖p‖ ≥ 1/2}`, because there the radial
projection and the cone time are honest continuous maps. -/
theorem continuousOn_coneMap {m : ℕ} {Y : Type*} [TopologicalSpace Y]
    (Φc : C(unitInterval × Sph m, Y)) (y₀ : Y) :
    ContinuousOn (coneMap Φc y₀)
      {p : Ball (m+1) | (1:ℝ)/2 ≤ ‖(p : EuclideanSpace ℝ (Fin (m+1)))‖} := by
  set s : Set (Ball (m+1)) := {p | (1:ℝ)/2 ≤ ‖(p : EuclideanSpace ℝ (Fin (m+1)))‖} with hs
  rw [continuousOn_iff_continuous_domRestrict]
  have hne : ∀ p : s, ((p.1 : Ball (m+1)) : EuclideanSpace ℝ (Fin (m+1))) ≠ 0 := by
    intro p hzero
    have hp : (1:ℝ)/2 ≤ ‖((p.1 : Ball (m+1)) : EuclideanSpace ℝ (Fin (m+1)))‖ := p.2
    rw [hzero, norm_zero] at hp
    norm_num at hp
  have hval : Continuous (fun p : s => ((p.1 : Ball (m+1)) : EuclideanSpace ℝ (Fin (m+1)))) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hinv : Continuous (fun p : s =>
      (‖((p.1 : Ball (m+1)) : EuclideanSpace ℝ (Fin (m+1)))‖)⁻¹) :=
    (continuous_norm.comp hval).inv₀ (fun p => norm_ne_zero_iff.mpr (hne p))
  let k : s → unitInterval × Sph m := fun p =>
    (coneTime ((p.1 : Ball (m+1)) : EuclideanSpace ℝ (Fin (m+1))),
     ⟨‖((p.1 : Ball (m+1)) : EuclideanSpace ℝ (Fin (m+1)))‖⁻¹ •
        ((p.1 : Ball (m+1)) : EuclideanSpace ℝ (Fin (m+1))),
      mem_Sph_iff.mpr (norm_inv_norm_smul (hne p))⟩)
  have hk : Continuous k := by
    unfold k
    refine Continuous.prodMk ?_ ?_
    · exact continuous_coneTime.comp hval
    · exact Continuous.subtype_mk (hinv.smul hval)
        (fun p => mem_Sph_iff.mpr (norm_inv_norm_smul (hne p)))
  refine (Φc.continuous.comp hk).congr (fun p => ?_)
  show Φc (k p) = coneMap Φc y₀ p.1
  unfold coneMap
  rw [dite_eq_right (hne p)]

/-- `ballConeMap` is continuous; gluing the constant piece on `{‖p‖ ≤ 1/2}` to the conical piece
on `{‖p‖ ≥ 1/2}` along the common closed boundary `{‖p‖ = 1/2}`. -/
theorem continuous_ballConeMap {m : ℕ} {Y : Type*} [TopologicalSpace Y]
    (Φc : C(unitInterval × Sph m, Y)) (y₀ : Y)
    (hc : ∀ x, Φc (1, x) = y₀) : Continuous (ballConeMap Φc y₀) := by
  rw [← continuousOn_univ]
  have hcover : {p : Ball (m+1) | (1:ℝ)/2 ≤ ‖(p : EuclideanSpace ℝ (Fin (m+1)))‖} ∪
      {p : Ball (m+1) | ‖(p : EuclideanSpace ℝ (Fin (m+1)))‖ ≤ (1:ℝ)/2} = Set.univ := by
    ext p
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    exact le_total ((1:ℝ)/2) ‖(p : EuclideanSpace ℝ (Fin (m+1)))‖
  rw [← hcover]
  have hs : IsClosed {p : Ball (m+1) | (1:ℝ)/2 ≤ ‖(p : EuclideanSpace ℝ (Fin (m+1)))‖} :=
    isClosed_le continuous_const (continuous_norm.comp continuous_subtype_val)
  have ht : IsClosed {p : Ball (m+1) | ‖(p : EuclideanSpace ℝ (Fin (m+1)))‖ ≤ (1:ℝ)/2} :=
    isClosed_le (continuous_norm.comp continuous_subtype_val) continuous_const
  rw [continuousOn_union_iff_of_isClosed hs ht]
  constructor
  · apply (continuousOn_coneMap Φc y₀).congr
    intro p hp
    have hp' : (1:ℝ)/2 ≤ ‖(p : EuclideanSpace ℝ (Fin (m+1)))‖ := hp
    unfold ballConeMap
    rw [ite_eq_left hp']
  · apply ContinuousOn.congr continuousOn_const
    intro p hp
    unfold ballConeMap
    by_cases h : (1:ℝ)/2 ≤ ‖(p : EuclideanSpace ℝ (Fin (m+1)))‖
    · rw [ite_eq_left h]
      unfold coneMap
      have hne : (p : EuclideanSpace ℝ (Fin (m+1))) ≠ 0 := by
        intro hzero; rw [hzero, norm_zero] at h; norm_num at h
      rw [dite_eq_right hne]
      have hle : ‖(p : EuclideanSpace ℝ (Fin (m+1)))‖ ≤ (1:ℝ)/2 := hp
      rw [coneTime_eq_one_of_norm_le hle]
      exact hc _
    · rw [ite_eq_right h]

/-- The sphere point of the ball is nonzero. -/
theorem sphToBall_ne_zero {m : ℕ} (x : Sph m) :
    ((SphToBall m x : Ball (m+1)) : EuclideanSpace ℝ (Fin (m+1))) ≠ 0 := by
  rw [coe_SphToBall]
  intro h
  have hh := mem_Sph_iff.mp x.2
  rw [h, norm_zero] at hh
  norm_num at hh

/-- On the unit sphere the conical map restricts to the original map: the cone time is `0` and the
radial projection is the identity. -/
theorem ballConeMap_sphere {m : ℕ} {Y : Type*} [TopologicalSpace Y]
    (Φc : C(unitInterval × Sph m, Y)) (y₀ : Y) (x : Sph m) :
    ballConeMap Φc y₀ (SphToBall m x) = Φc (0, x) := by
  have hnorm : ‖((SphToBall m x : Ball (m+1)) : EuclideanSpace ℝ (Fin (m+1)))‖ = 1 := by
    rw [coe_SphToBall]; exact mem_Sph_iff.mp x.2
  have hge : (1:ℝ)/2 ≤ ‖((SphToBall m x : Ball (m+1)) : EuclideanSpace ℝ (Fin (m+1)))‖ := by
    rw [hnorm]; norm_num
  unfold ballConeMap
  rw [ite_eq_left hge]
  unfold coneMap
  rw [dite_eq_right (sphToBall_ne_zero x)]
  have htime : coneTime ((SphToBall m x : Ball (m+1)) : EuclideanSpace ℝ (Fin (m+1))) = 0 := by
    rw [coe_SphToBall]; exact coneTime_eq_zero_of_norm_eq_one (mem_Sph_iff.mp x.2)
  have hrad : (⟨‖((SphToBall m x : Ball (m+1)) : EuclideanSpace ℝ (Fin (m+1)))‖⁻¹ •
      ((SphToBall m x : Ball (m+1)) : EuclideanSpace ℝ (Fin (m+1))),
      mem_Sph_iff.mpr (norm_inv_norm_smul (sphToBall_ne_zero x))⟩ : Sph m) = x := by
    apply Subtype.ext
    change (‖((SphToBall m x : Ball (m+1)) : EuclideanSpace ℝ (Fin (m+1)))‖)⁻¹ •
      ((SphToBall m x : Ball (m+1)) : EuclideanSpace ℝ (Fin (m+1))) =
        (x : EuclideanSpace ℝ (Fin (m+1)))
    rw [coe_SphToBall]
    exact inv_norm_smul_self_of_norm_eq_one (mem_Sph_iff.mp x.2)
  rw [htime, hrad]

/-- A map `g : 𝕊ᵐ → Y` that is homotopic to a constant map extends continuously over the closed
ball `𝔻ᵐ⁺¹`: a null-homotopy is a map on the cone on `𝕊ᵐ`, and the cone on `𝕊ᵐ` is the ball.
`SphToBall m : C(Sph m, Ball (m+1))` is the inclusion of the unit sphere into the unit ball of the
same ambient space `ℝᵐ⁺¹` (both from `Work.Conn.Basic`).

Route.  Unpack `H` into `Φ : C(Sph m × unitInterval, Y)` with `Φ (x, 0) = g x` and
`Φ (x, 1) = y₀`.  Choose a base point `e₀ : Sph m` and define a total function
`φ : ℝᵐ⁺¹ → Sph m` by `φ x = ⟨‖x‖⁻¹ • x, _⟩` when `x ≠ 0` and `φ 0 = e₀`, and let
`τ x = min (2 * (1 - ‖x‖)) 1` clamped into `[0,1]`.  Then `G₀ x := Φ (φ x, τ x)` equals `y₀`
on `{‖x‖ ≤ 1/2}`, equals `Φ (‖x‖⁻¹ • x, 2 * (1 - ‖x‖))` on `{1/2 ≤ ‖x‖}`, and on the unit sphere
`τ x = 0`, `φ x = x`, so `G₀ x = g x`.  The two pieces are continuous on their (closed) domains —
the first is constant, the second is a composite of `Φ` with continuous maps (legitimate there
since `‖x‖ ≥ 1/2`) — so `G₀` is continuous by gluing on the closed cover
`{‖x‖ ≤ 1/2} ∪ {1/2 ≤ ‖x‖}` (`continuous_if`, or `nhdsWithin_union` plus
`ContinuousWithinAt.continuousAt`; note that `φ` itself is discontinuous at `0`), and restricting
to `Ball (m+1)` gives the required `G`. -/
theorem exists_continuousMap_ball_of_homotopic_const {m : ℕ} {Y : Type*} [TopologicalSpace Y]
    (g : C(Sph m, Y)) (y₀ : Y) (H : g.Homotopic (ContinuousMap.const (Sph m) y₀)) :
    ∃ G : C(Ball (m + 1), Y), G.comp (SphToBall m) = g := by
  obtain ⟨Φ⟩ := H
  have hc : ∀ x, Φ.toContinuousMap (1, x) = y₀ := fun _ => by simp
  refine ⟨⟨ballConeMap Φ.toContinuousMap y₀,
    continuous_ballConeMap Φ.toContinuousMap y₀ hc⟩, ?_⟩
  apply ContinuousMap.ext
  intro x
  exact (ballConeMap_sphere Φ.toContinuousMap y₀ x).trans (Φ.map_zero_left x)

end

end Work.Conn.Extend
