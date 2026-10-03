import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.bl_geom_basic
import Submission.Work.L62.tau0_piExp_image_isOpen
import Submission.Work.L62.tau0_Bl_ball

/-!
# `Work.L62.tau0_Bl_geometry` — the cylinder neighbourhood `{0} ∪ τ₀(π(B^ℓ))` of the lower end

`π w = e^{2πiw}`, `τ₀ w = -1/w`, and `Bl` is the lower component of `φ₀⁻¹(B)` (`HornData.Bl`):
the component of the maximal lift domain through the lower end, with
`{w : w.im < -η} ⊆ Bl`, `Bl ⊆ {w : w.im ≤ η}` and `Bl` connected (and `T`-invariant).

Because `‖τ₀ (π w)‖ = e^{2π Im w}`, the lower end `Im w → -∞` corresponds to `π`-images tending to
`0`, so the set `{0} ∪ τ₀(π(Bl))` is a full neighbourhood of `0` in the cylinder: it contains the
punctured disc of radius `e^{-2πη}` and lies in the closed disc of radius `e^{2πη}`.  It is open
(`τ₀ ∘ π` is a local homeomorphism, `Bl` is open), bounded (`Bl ⊆ {Im ≤ η}`) and preconnected
(image of the connected `Bl`, together with the convex ball it meets).

This file proves the geometry; the two pieces `Work.L62.tau0_piExp_image_isOpen` and
`Work.L62.tau0_Bl_ball` are proved separately and imported.
-/

namespace Work.L62

open MandelDim Set Filter Topology Metric
open scoped Topology

noncomputable section

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

/-- `{0} ∪ τ₀(π(Bl)) ⊆ closedBall 0 (e^{2πη})`: for `w ∈ Bl`, `‖τ₀ (π w)‖ = e^{2π Im w} ≤ e^{2πη}`
because `Bl ⊆ {Im ≤ η}` (otherwise `Bl` would meet the upper component `Bu`). -/
theorem subset_closedBall_insert_tau0_Bl (d : ParabData g₀ D) (hd : HornData d) :
    insert 0 (tau0 '' (piExp '' hd.Bl)) ⊆ closedBall 0 (Real.exp (2 * Real.pi * hd.η)) := by
  rintro ζ (rfl | ⟨w, ⟨u, hu, rfl⟩, rfl⟩)
  · exact mem_closedBall_self (Real.exp_pos _).le
  · rw [mem_closedBall_zero_iff, norm_tau0_piExp]
    have him := Bl_im_le d hd hu
    exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, him])

/-- `{0} ∪ τ₀(π(Bl))` is bounded (it is contained in the closed disc of radius `e^{2πη}`). -/
theorem isBounded_insert_tau0_Bl (d : ParabData g₀ D) (hd : HornData d) :
    Bornology.IsBounded (insert 0 (tau0 '' (piExp '' hd.Bl))) :=
  (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mpr
    ⟨Real.exp (2 * Real.pi * hd.η), subset_closedBall_insert_tau0_Bl d hd⟩

/-- `{0} ∪ τ₀(π(Bl))` is preconnected: it is the union of `τ₀(π(Bl))`, the continuous image of
the connected set `Bl`, and of the convex ball `ball 0 (e^{-2πη})`, which meet at the point
`τ₀(π(-i(η+1)))` (of modulus `e^{-2π(η+1)} < e^{-2πη}`). -/
theorem preconnected_insert_tau0_Bl (d : ParabData g₀ D) (hd : HornData d) :
    IsPreconnected (insert 0 (tau0 '' (piExp '' hd.Bl))) := by
  have hA : IsPreconnected (tau0 '' (piExp '' hd.Bl)) := by
    have h := hd.Bl_conn.isPreconnected.image (fun w => tau0 (piExp w))
      continuous_tau0_piExp.continuousOn
    have h2 : (fun w : ℂ => tau0 (piExp w)) '' hd.Bl = tau0 '' (piExp '' hd.Bl) := by
      rw [show (fun w : ℂ => tau0 (piExp w)) = tau0 ∘ piExp from rfl, Set.image_comp]
    rwa [h2] at h
  have hball : IsPreconnected (ball (0 : ℂ) (Real.exp (-(2 * Real.pi * hd.η)))) :=
    (convex_ball (0 : ℂ) _).isPreconnected
  set w₀ : ℂ := -(Complex.I * ((hd.η + 1 : ℝ) : ℂ)) with hw₀def
  have hw₀ : w₀ ∈ hd.Bl := hd.lower (by simp [w₀, Complex.mul_im])
  have hz₀A : tau0 (piExp w₀) ∈ tau0 '' (piExp '' hd.Bl) :=
    ⟨piExp w₀, ⟨w₀, hw₀, rfl⟩, rfl⟩
  have hz₀B : tau0 (piExp w₀) ∈ ball (0 : ℂ) (Real.exp (-(2 * Real.pi * hd.η))) := by
    rw [mem_ball_zero_iff, norm_tau0_piExp]
    apply Real.exp_lt_exp.mpr
    have hw₀im : w₀.im = -(hd.η + 1) := by simp [w₀, Complex.mul_im]
    rw [hw₀im]
    nlinarith [Real.pi_pos]
  have hEq : insert 0 (tau0 '' (piExp '' hd.Bl))
      = ball (0 : ℂ) (Real.exp (-(2 * Real.pi * hd.η))) ∪ tau0 '' (piExp '' hd.Bl) := by
    apply Subset.antisymm
    · rintro ζ (rfl | hζ)
      · exact Or.inl (mem_ball_self (Real.exp_pos _))
      · exact Or.inr hζ
    · rintro ζ (hζ | hζ)
      · exact tau0_Bl_ball d hd hζ
      · exact mem_insert_iff.mpr (Or.inr hζ)
  rw [hEq]
  exact IsPreconnected.union _ hz₀B hz₀A hball hA

/-- **The lower end of the horn map, as a neighbourhood of `0` in the cylinder.**  For the lower
component `Bl` of `φ₀⁻¹(B)`, the set `{0} ∪ τ₀(π(Bl))` is an open, bounded, preconnected subset
of `ℂ` containing the punctured disc of radius `e^{-2πη}` and contained in the closed disc of
radius `e^{2πη}`. -/
theorem tau0_Bl_geometry {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) :
    IsOpen (insert 0 (MandelDim.tau0 '' (MandelDim.piExp '' hd.Bl))) ∧
    Bornology.IsBounded (insert 0 (MandelDim.tau0 '' (MandelDim.piExp '' hd.Bl))) ∧
    IsPreconnected (insert 0 (MandelDim.tau0 '' (MandelDim.piExp '' hd.Bl))) ∧
    Metric.ball 0 (Real.exp (-(2 * Real.pi * hd.η))) ⊆
      insert 0 (MandelDim.tau0 '' (MandelDim.piExp '' hd.Bl)) ∧
    insert 0 (MandelDim.tau0 '' (MandelDim.piExp '' hd.Bl)) ⊆
      Metric.closedBall 0 (Real.exp (2 * Real.pi * hd.η)) := by
  have hEq : insert 0 (tau0 '' (piExp '' hd.Bl))
      = ball (0 : ℂ) (Real.exp (-(2 * Real.pi * hd.η))) ∪ tau0 '' (piExp '' hd.Bl) := by
    apply Subset.antisymm
    · rintro ζ (rfl | hζ)
      · exact Or.inl (mem_ball_self (Real.exp_pos _))
      · exact Or.inr hζ
    · rintro ζ (hζ | hζ)
      · exact tau0_Bl_ball d hd hζ
      · exact mem_insert_iff.mpr (Or.inr hζ)
  refine ⟨?_, isBounded_insert_tau0_Bl d hd, preconnected_insert_tau0_Bl d hd,
    tau0_Bl_ball d hd, subset_closedBall_insert_tau0_Bl d hd⟩
  rw [hEq]
  exact isOpen_ball.union (tau0_piExp_image_isOpen hd.Bl_open)

end

end Work.L62
