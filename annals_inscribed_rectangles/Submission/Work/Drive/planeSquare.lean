import Mathlib
import Submission.Work.Drive.squareDisk
import Submission.Work.Drive.cappedPlaneCharts
import Submission.Work.Drive.sqDisk_surjective
import Submission.Work.Drive.sqDisk_injective

/-!
# The capped plane as a box map, with its seam invariance

`Submission/Work/Drive/squareDisk.lean` supplies the globally smooth square-to-disk map `sqDisk` whose
boundary identification is the antipodal map of the disk's boundary circle.  Composing it with the disk
presentation of the capped plane (`Work.Drive.diskPt`,
`Submission/Work/Drive/cappedPlaneCharts.lean`) turns the plane `P_u = u·M ∪ cap_u` into a map

> `planeSq y = diskPt (sqDisk y)`

on the square `[0,1]²`, whose boundary is identified by the antipodal involution
`Work.Drive.seamInv2 : (y₀,y₁) ↦ (1-y₀,1-y₁)` of the square.  This is exactly the hypothesis the
sweep-seam machinery consumes (`Work.Drive.sweepChain_seamInv`,
`Work.Drive.triple_seamInv_of_plane_seamInv`, `Work.Drive.manifold_triple_seam_cancel`): the four
*seam* faces of the parameter cube of the sweep pair up, so they contribute evenly to the boundary
triple count.

To make the map total (so that `sweepChain` of it is defined on all of `ℝ³`) the square coordinate is
first clamped into `[0,1]²` by `clampBox`; on the unit square the clamp is the identity, so the
restriction of `planeSq` to the square is the disk presentation itself
(`Work.Drive.planeSq_eq_diskPt`).  The clamp is also compatible with the seam involution
(`Work.Drive.clampBox_seamInv`), which is what makes the seam invariance hold for *every* point of the
seam, as `manifold_triple_seam_cancel` requires.
-/

set_option autoImplicit false

namespace Work.Drive

open scoped Topology ContDiff
open Manifold

noncomputable section

open Submission.Configuration (muOrd)

/-! ## The clamping of the square into the unit square -/

/-- **The clamping of the square into `[0,1]²`.**  Used only to make the plane map total on `ℝ²`; it
is the identity on the unit square and commutes with the seam involution. -/
def clampBox (y : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  mk2 (max 0 (min 1 (y 0))) (max 0 (min 1 (y 1)))

@[simp] lemma clampBox_apply_zero (y : EuclideanSpace ℝ (Fin 2)) :
    clampBox y 0 = max 0 (min 1 (y 0)) := rfl

@[simp] lemma clampBox_apply_one (y : EuclideanSpace ℝ (Fin 2)) :
    clampBox y 1 = max 0 (min 1 (y 1)) := rfl

lemma clampBox_mem_unitBox (y : EuclideanSpace ℝ (Fin 2)) :
    clampBox y ∈ Submission.Drive.unitBox 1 := by
  intro i
  fin_cases i
  · exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  · exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

lemma clampBox_eq_self {y : EuclideanSpace ℝ (Fin 2)} (hy : y ∈ Submission.Drive.unitBox 1) :
    clampBox y = y := by
  have h0 := hy 0
  have h1 := hy 1
  rw [Set.mem_Icc] at h0 h1
  ext i
  fin_cases i
  · show max 0 (min 1 (y 0)) = y 0
    rw [min_eq_right h0.2, max_eq_right h0.1]
  · show max 0 (min 1 (y 1)) = y 1
    rw [min_eq_right h1.2, max_eq_right h1.1]

/-- The clamping commutes with the reflection `t ↦ 1 - t` of the interval: this is what makes it
compatible with the seam involution. -/
lemma max_min_clamp_compl (t : ℝ) : max 0 (min 1 (1 - t)) = 1 - max 0 (min 1 t) := by
  rcases le_total t 0 with h | h
  · rw [min_eq_left (by linarith : (1 : ℝ) ≤ 1 - t), max_eq_right (by norm_num : (0:ℝ) ≤ 1),
      min_eq_right (by linarith : t ≤ 1), max_eq_left h]
    norm_num
  · rcases le_total 1 t with h1 | h1
    · rw [min_eq_right (by linarith : 1 - t ≤ 1), max_eq_left (by linarith : 1 - t ≤ 0),
        min_eq_left h1, max_eq_right (by norm_num : (0:ℝ) ≤ 1)]
      norm_num
    · rw [min_eq_right (by linarith : 1 - t ≤ 1), max_eq_right (by linarith : (0:ℝ) ≤ 1 - t),
        min_eq_right h1, max_eq_right h]

@[simp] lemma clampBox_seamInv (y : EuclideanSpace ℝ (Fin 2)) :
    clampBox (seamInv2 y) = seamInv2 (clampBox y) := by
  ext i
  fin_cases i
  · show max 0 (min 1 ((seamInv2 y) 0)) = 1 - max 0 (min 1 (y 0))
    rw [seamInv2_apply_zero, max_min_clamp_compl]
  · show max 0 (min 1 ((seamInv2 y) 1)) = 1 - max 0 (min 1 (y 1))
    rw [seamInv2_apply_one, max_min_clamp_compl]

lemma onSeam2_clampBox {y : EuclideanSpace ℝ (Fin 2)} (hy : onSeam2 y) :
    onSeam2 (clampBox y) := by
  rcases hy with h | h | h | h
  · exact Or.inl (by rw [clampBox_apply_zero, h]; norm_num)
  · exact Or.inr (Or.inl (by rw [clampBox_apply_zero, h]; norm_num))
  · exact Or.inr (Or.inr (Or.inl (by rw [clampBox_apply_one, h]; norm_num)))
  · exact Or.inr (Or.inr (Or.inr (by rw [clampBox_apply_one, h]; norm_num)))

/-! ## The disk presentation depends on the point of the disk only -/

section ProofIrrel

variable {γ : Circle → ℝ × ℝ}
variable {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ}
variable {ρ Ψ Θ : ℝ → ℝ} {r₀ : ℝ} {u : UnitAddCircle}

/-- The disk presentation of the capped plane depends on the point of the disk only, not on the proof
of its side condition `‖z‖ ≤ 1`. -/
lemma diskPt_proof_irrel (hr₀ : 0 < r₀) (hρ : ∀ t : ℝ, 0 < ρ t)
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    {z : ℂ} (h1 h2 : ‖z‖ ≤ 1) :
    diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag z h1
      = diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag z h2 := by
  by_cases h : ‖z‖ < 1 / 2
  · calc diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag z h1
        = capDiskPt r₀ ρ Ψ Θ u hr₀ hρ z h := diskPt_of_lt (hz1 := h1) h
      _ = diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag z h2 :=
          (diskPt_of_lt (hz1 := h2) h).symm
  · calc diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag z h1
        = stripDiskPt μ u hγne hγinj hμne hμdiag z (le_of_not_gt h) h1 :=
          diskPt_of_ge (hz1 := h1) (le_of_not_gt h)
      _ = diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag z h2 :=
          (diskPt_of_ge (hz1 := h2) (le_of_not_gt h)).symm

/-- **The disk presentation is invariant under equality of the point of the disk.** -/
lemma diskPt_congr (hr₀ : 0 < r₀) (hρ : ∀ t : ℝ, 0 < ρ t)
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    {z z' : ℂ} (hzz : z = z') (h1 : ‖z‖ ≤ 1) (h2 : ‖z'‖ ≤ 1) :
    diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag z h1
      = diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag z' h2 := by
  cases hzz
  exact diskPt_proof_irrel hr₀ hρ hγne hγinj hμne hμdiag h1 h2

end ProofIrrel

/-! ## The plane as a box map -/

/-- **The capped plane `P_u` as a map on the square.**  The disk presentation `Work.Drive.diskPt`
composed with the square-to-disk map `Work.Drive.sqDisk`, with the square coordinate clamped into
`[0,1]²` so that the map is defined on all of `ℝ²`.  On the unit square the clamp is the identity, so
this is literally the disk presentation of `P_u`. -/
def planeSq {γ : Circle → ℝ × ℝ}
    (μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ) (ρ Ψ Θ : ℝ → ℝ) (r₀ : ℝ)
    (u : UnitAddCircle) (hr₀ : 0 < r₀) (hρ : ∀ t : ℝ, 0 < ρ t)
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    (y : EuclideanSpace ℝ (Fin 2)) : CappingSpace :=
  diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag (sqDisk (clampBox y))
    (norm_sqDisk_le_one _ (clampBox_mem_unitBox y))

/-- **On the unit square the clamped plane map is the disk presentation of the capped plane.** -/
theorem planeSq_eq_diskPt {γ : Circle → ℝ × ℝ}
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ} {ρ Ψ Θ : ℝ → ℝ} {r₀ : ℝ}
    {u : UnitAddCircle} {hr₀ : 0 < r₀} {hρ : ∀ t : ℝ, 0 < ρ t}
    {hγne : ∀ x : Circle, γ x ≠ 0} {hγinj : Function.Injective γ}
    {hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = muOrd γ (x, y)}
    {hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0)}
    {y : EuclideanSpace ℝ (Fin 2)} (hy : y ∈ Submission.Drive.unitBox 1) :
    planeSq μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag y
      = diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag (sqDisk y)
          (norm_sqDisk_le_one y hy) := by
  rw [planeSq]
  exact diskPt_congr hr₀ hρ hγne hγinj hμne hμdiag
    (congrArg sqDisk (clampBox_eq_self hy)) _ _

/-- **The seam invariance of the plane map.**  On the boundary of the square the involution
`seamInv2` of the parameters does not change the point of the capped plane: the two square points are
antipodal points of the disk's boundary circle, where the disk presentation `diskPt` identifies them
(`Work.Drive.diskPt_eq_iff`).  Together with `Work.Drive.sqDisk_seamInv` this is the geometric content
of the capping's boundary identification. -/
theorem planeSq_seamInv {γ : Circle → ℝ × ℝ}
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ} {ρ Ψ Θ : ℝ → ℝ} {r₀ : ℝ}
    {u : UnitAddCircle} (hr₀ : 0 < r₀) (hρ : ∀ t : ℝ, 0 < ρ t)
    (hpolar : ∀ t : ℝ, polarLift (ρ t, Ψ t) = γ (Circle.exp t))
    (hΘper : ∀ t : ℝ, Θ (t + 2 * Real.pi) = Θ t)
    (hΘclass : ∀ t : ℝ, ((Θ t : ℝ) : UnitAddCircle)
      = tangentDirC γ (Circle.exp t) - 2 • ((Ψ t : ℝ) : UnitAddCircle))
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    (hsym : ∀ x y : Circle, μ (y, x) = μ (x, y))
    (hinj : ∀ x y x' y' : Circle, μ (x, y) = μ (x', y') →
      (x = x' ∧ y = y') ∨ (x = y' ∧ y = x'))
    (y : EuclideanSpace ℝ (Fin 2)) (hy : onSeam2 y) :
    planeSq μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag y
      = planeSq μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag (seamInv2 y) := by
  have hbox : clampBox y ∈ Submission.Drive.unitBox 1 := clampBox_mem_unitBox y
  have hseam : onSeam2 (clampBox y) := onSeam2_clampBox hy
  have hz1 : ‖sqDisk (clampBox y)‖ ≤ 1 := norm_sqDisk_le_one _ hbox
  have hzn : ‖sqDisk (clampBox y)‖ = 1 := (norm_sqDisk_eq_one_iff _ hbox).mpr hseam
  have hz2 : ‖-sqDisk (clampBox y)‖ ≤ 1 := by rw [norm_neg]; exact hz1
  have hiff : diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag (sqDisk (clampBox y)) hz1
      = diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag (- sqDisk (clampBox y)) hz2 :=
    ((cappedPlane_diskPresentation_of_polarLift (γ := γ) (μ := μ) (ρ := ρ) (Ψ := Ψ) (Θ := Θ)
        (r₀ := r₀) (u := u) hr₀ hρ hpolar hΘper hΘclass hγne hγinj hμne hμdiag hsym hinj).2
      (sqDisk (clampBox y)) (- sqDisk (clampBox y)) hz1 hz2).mpr
      (Or.inr ⟨hzn, by rw [norm_neg, hzn], rfl⟩)
  have hneg : sqDisk (seamInv2 (clampBox y)) = - sqDisk (clampBox y) := sqDisk_seamInv _
  have hz1' : ‖sqDisk (seamInv2 (clampBox y))‖ ≤ 1 := by rw [hneg, norm_neg]; exact hz1
  have hc : ‖sqDisk (clampBox (seamInv2 y))‖ ≤ 1 :=
    norm_sqDisk_le_one _ (clampBox_mem_unitBox (seamInv2 y))
  calc planeSq μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag y
      = diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag (sqDisk (clampBox y)) hz1 := rfl
    _ = diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag (- sqDisk (clampBox y)) hz2 := hiff
    _ = diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag
          (sqDisk (seamInv2 (clampBox y))) hz1' :=
        diskPt_congr hr₀ hρ hγne hγinj hμne hμdiag hneg.symm hz2 hz1'
    _ = diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag (sqDisk (clampBox (seamInv2 y))) hc :=
        diskPt_congr hr₀ hρ hγne hγinj hμne hμdiag
          (congrArg sqDisk (clampBox_seamInv y)).symm hz1' hc
    _ = planeSq μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag (seamInv2 y) := rfl

/-- **The sweep of the plane is seam-invariant.**  The `hseam` hypothesis of
`Work.Drive.manifold_triple_seam_cancel` for the three sweeps of the capped planes
`P_{u 0}, P_{u 1}, P_{u 2}`: each sweep agrees with itself under the antipodal involution
`Work.Drive.seamInv` of the parameter cube on the four seam faces. -/
theorem planeSq_triple_seamInv {γ : Circle → ℝ × ℝ}
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ} {ρ Ψ Θ : ℝ → ℝ} {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hρ : ∀ t : ℝ, 0 < ρ t)
    (hpolar : ∀ t : ℝ, polarLift (ρ t, Ψ t) = γ (Circle.exp t))
    (hΘper : ∀ t : ℝ, Θ (t + 2 * Real.pi) = Θ t)
    (hΘclass : ∀ t : ℝ, ((Θ t : ℝ) : UnitAddCircle)
      = tangentDirC γ (Circle.exp t) - 2 • ((Ψ t : ℝ) : UnitAddCircle))
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    (hsym : ∀ x y : Circle, μ (y, x) = μ (x, y))
    (hinj : ∀ x y x' y' : Circle, μ (x, y) = μ (x', y') →
      (x = x' ∧ y = y') ∨ (x = y' ∧ y = x'))
    (a : Fin 3 → ℝ) (ha : ∀ k, 0 < a k) (u : Fin 3 → UnitAddCircle) :
    ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)), onSeam x →
      sweepChain (a k) (ha k) (planeSq μ ρ Ψ Θ r₀ (u k) hr₀ hρ hγne hγinj hμne hμdiag) x
        = sweepChain (a k) (ha k) (planeSq μ ρ Ψ Θ r₀ (u k) hr₀ hρ hγne hγinj hμne hμdiag)
            (seamInv x) :=
  triple_seamInv_of_plane_seamInv a ha
    (fun k => planeSq μ ρ Ψ Θ r₀ (u k) hr₀ hρ hγne hγinj hμne hμdiag)
    (fun _ y hy => planeSq_seamInv hr₀ hρ hpolar hΘper hΘclass hγne hγinj hμne hμdiag hsym hinj y hy)

end

end Work.Drive

namespace Work.Drive

open scoped Topology ContDiff
open Manifold

noncomputable section

open Submission.Configuration (muOrd)

/-- **The seam of the square presentation is the cut of the capped plane.**  On the boundary of the
square the plane map lands on the core loop `Work.Drive.coreLoopPt` of the configuration Möbius band —
the projective line `C_0` of `P_u` that cuts `P_u` into an open disk
(`Submission/Work/Drive/SWEEP_TRANSPORT_NOTES.md` §3).  Explicitly, the seam point `y` maps to the
diametral configuration at parameter `arg (sqDisk y) / π`. -/
theorem planeSq_seam_eq_core {γ : Circle → ℝ × ℝ}
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ} {ρ Ψ Θ : ℝ → ℝ} {r₀ : ℝ}
    {u : UnitAddCircle} {hr₀ : 0 < r₀} {hρ : ∀ t : ℝ, 0 < ρ t}
    {hγne : ∀ x : Circle, γ x ≠ 0} {hγinj : Function.Injective γ}
    {hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = muOrd γ (x, y)}
    {hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0)}
    (y : EuclideanSpace ℝ (Fin 2)) (hy : onSeam2 y) :
    planeSq μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag y
      = rotCapping u (Quotient.mk'' (Sum.inl (confPiece
          (coreLoopPt γ (Complex.arg (sqDisk (clampBox y)) / Real.pi))
          (confOf_fst_pos_of_len_pos (coreLoopPt_len_pos hγinj _))
          (confOf_snd_norm_le_one _)) : ConfigPiece ⊕ CapPiece)) := by
  have hbox : clampBox y ∈ Submission.Drive.unitBox 1 := clampBox_mem_unitBox y
  have hseam : onSeam2 (clampBox y) := onSeam2_clampBox hy
  have hzn : ‖sqDisk (clampBox y)‖ = 1 := (norm_sqDisk_eq_one_iff _ hbox).mpr hseam
  have hz1 : ‖sqDisk (clampBox y)‖ ≤ 1 := norm_sqDisk_le_one _ hbox
  rw [planeSq]
  exact diskPt_boundary_eq_core hμne hγinj hzn hz1

end

end Work.Drive

namespace Work.Drive

open scoped Topology ContDiff
open Manifold

noncomputable section

open Submission.Configuration (muOrd)

/-- The seam involution `Work.Drive.seamInv2` preserves the unit square. -/
lemma seamInv2_mem_unitBox {y : EuclideanSpace ℝ (Fin 2)} (hy : y ∈ Submission.Drive.unitBox 1) :
    seamInv2 y ∈ Submission.Drive.unitBox 1 := by
  intro i
  fin_cases i
  · show (1 - y 0 : ℝ) ∈ Set.Icc (0 : ℝ) 1
    have h := hy 0
    rw [Set.mem_Icc] at h ⊢
    exact ⟨by linarith [h.2], by linarith [h.1]⟩
  · show (1 - y 1 : ℝ) ∈ Set.Icc (0 : ℝ) 1
    have h := hy 1
    rw [Set.mem_Icc] at h ⊢
    exact ⟨by linarith [h.2], by linarith [h.1]⟩

/-- **The box presentation of the capped plane is onto the plane.**  Every point of
`P_u = u·M ∪ cap_u` is the image of a point of the unit square under the plane map
`Work.Drive.planeSq`. -/
theorem planeSq_range {γ : Circle → ℝ × ℝ}
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ} {ρ Ψ Θ : ℝ → ℝ} {r₀ : ℝ}
    {u : UnitAddCircle} (hr₀ : 0 < r₀) (hρ : ∀ t : ℝ, 0 < ρ t)
    (hpolar : ∀ t : ℝ, polarLift (ρ t, Ψ t) = γ (Circle.exp t))
    (hΘper : ∀ t : ℝ, Θ (t + 2 * Real.pi) = Θ t)
    (hΘclass : ∀ t : ℝ, ((Θ t : ℝ) : UnitAddCircle)
      = tangentDirC γ (Circle.exp t) - 2 • ((Ψ t : ℝ) : UnitAddCircle))
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    (hsym : ∀ x y : Circle, μ (y, x) = μ (x, y))
    (hinj : ∀ x y x' y' : Circle, μ (x, y) = μ (x', y') →
      (x = x' ∧ y = y') ∨ (x = y' ∧ y = x')) :
    Set.range (fun y : {y : EuclideanSpace ℝ (Fin 2) // y ∈ Submission.Drive.unitBox 1} =>
        planeSq μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag y.1)
      = cappedPlane r₀ ρ Ψ Θ μ u := by
  ext p
  constructor
  · rintro ⟨y, rfl⟩
    exact diskPt_mem hr₀ hρ hγne hγinj hμne hμdiag _
  · intro hp
    obtain ⟨z, hz, hzeq⟩ := exists_diskPt_eq_of_mem
      (polarLift_periodic_of_eq hρ hpolar).1 (polarLift_periodic_of_eq hρ hpolar).2 hΘper hr₀ hρ
      hpolar hΘclass hγne hγinj hμne hμdiag hsym hinj hp
    obtain ⟨y, hy, hysq⟩ := sqDisk_surjective z hz
    refine ⟨⟨y, hy⟩, ?_⟩
    change planeSq μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag y = p
    rw [planeSq_eq_diskPt hy]
    exact (diskPt_congr hr₀ hρ hγne hγinj hμne hμdiag hysq (norm_sqDisk_le_one y hy) hz).trans hzeq

/-- **The box presentation of the capped plane is faithful.**  Two points of the unit square give the
same point of the capped plane exactly when they are equal or are the two presentations of the same
point of the seam: this is the multiplicity-one (odd, in particular) property that the parity
bookkeeping of `Work.Drive.manifold_triple_inter_boundary_parity` needs of the plane's own `2`-chain
(`top_k` is the paper's `n_{P_k}` only if the presentation does not cover the plane an even number of
times). -/
theorem planeSq_eq_iff {γ : Circle → ℝ × ℝ}
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ} {ρ Ψ Θ : ℝ → ℝ} {r₀ : ℝ}
    {u : UnitAddCircle} (hr₀ : 0 < r₀) (hρ : ∀ t : ℝ, 0 < ρ t)
    (hpolar : ∀ t : ℝ, polarLift (ρ t, Ψ t) = γ (Circle.exp t))
    (hΘper : ∀ t : ℝ, Θ (t + 2 * Real.pi) = Θ t)
    (hΘclass : ∀ t : ℝ, ((Θ t : ℝ) : UnitAddCircle)
      = tangentDirC γ (Circle.exp t) - 2 • ((Ψ t : ℝ) : UnitAddCircle))
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    (hsym : ∀ x y : Circle, μ (y, x) = μ (x, y))
    (hinj : ∀ x y x' y' : Circle, μ (x, y) = μ (x', y') →
      (x = x' ∧ y = y') ∨ (x = y' ∧ y = x'))
    (y y' : EuclideanSpace ℝ (Fin 2)) (hy : y ∈ Submission.Drive.unitBox 1)
    (hy' : y' ∈ Submission.Drive.unitBox 1) :
    planeSq μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag y
        = planeSq μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag y'
      ↔ y = y' ∨ (onSeam2 y ∧ y' = seamInv2 y) := by
  have hiff := (cappedPlane_diskPresentation_of_polarLift (γ := γ) (μ := μ) (ρ := ρ) (Ψ := Ψ)
      (Θ := Θ) (r₀ := r₀) (u := u) hr₀ hρ hpolar hΘper hΘclass hγne hγinj hμne hμdiag hsym
      hinj).2
  rw [planeSq_eq_diskPt hy, planeSq_eq_diskPt hy']
  constructor
  · intro h
    rcases (hiff (sqDisk y) (sqDisk y') (norm_sqDisk_le_one y hy)
      (norm_sqDisk_le_one y' hy')).mp h with hzz | ⟨h1, h2, hneg⟩
    · exact Or.inl (sqDisk_injective y y' hy hy' hzz)
    · exact Or.inr ⟨(norm_sqDisk_eq_one_iff y hy).mp h1,
        sqDisk_injective y' (seamInv2 y) hy' (seamInv2_mem_unitBox hy)
          (by rw [hneg, sqDisk_seamInv])⟩
  · rintro (rfl | ⟨hseam, rfl⟩)
    · rfl
    · have hn : ‖sqDisk y‖ = 1 := (norm_sqDisk_eq_one_iff y hy).mpr hseam
      refine (hiff (sqDisk y) (sqDisk (seamInv2 y)) (norm_sqDisk_le_one y hy)
        (norm_sqDisk_le_one (seamInv2 y) (seamInv2_mem_unitBox hy))).mpr (Or.inr ⟨hn, ?_, ?_⟩)
      · rw [sqDisk_seamInv, norm_neg]; exact hn
      · exact sqDisk_seamInv y

end

end Work.Drive

namespace Work.Drive

open scoped Topology ContDiff
open Manifold

noncomputable section

open Submission.Configuration (muOrd)
