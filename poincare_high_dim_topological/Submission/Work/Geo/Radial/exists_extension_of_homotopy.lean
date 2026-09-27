import Mathlib
import Submission.Work.Conn.Basic
import Submission.Work.Conn.Extend.exists_continuousMap_ball_of_homotopic_const

namespace Work.Geo.Radial

open Set Metric
open ContinuousMap
open Work.Conn

/-- If `f₀` is homotopic to `f₁` and `f₁` extends over the disc, then so does `f₀`.

The intended fully-qualified name is `Work.Geo.Radial.exists_extension_of_homotopy` (file
`Submission/Work/Geo/Radial/exists_extension_of_homotopy.lean`). -/
theorem exists_extension_of_homotopy {j : ℕ} {Y : Type*} [TopologicalSpace Y]
    {f₀ f₁ : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (j + 1))) 1, Y)} (h : f₀.Homotopic f₁)
    (g : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin (j + 1))) 1, Y))
    (hg : ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (j + 1))) 1,
      g ⟨x.1, Metric.sphere_subset_closedBall x.2⟩ = f₁ x) :
    ∃ G : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin (j + 1))) 1, Y),
      ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (j + 1))) 1,
        G ⟨x.1, Metric.sphere_subset_closedBall x.2⟩ = f₀ x := by
  classical
  -- the centre of the disc
  let c : Ball (j + 1) := ⟨0, by simp⟩
  -- the vector field `p ↦ (1 - p.1) • p.2` lies in the disc (linear shrinking of the sphere)
  have hmem : ∀ p : unitInterval × Sph j,
      (1 - ((p.1 : unitInterval) : ℝ)) •
        ((p.2 : Sph j) : EuclideanSpace ℝ (Fin (j + 1))) ∈ Ball (j + 1) := by
    intro p
    rw [mem_Ball_iff, norm_smul, Real.norm_eq_abs, norm_coe_Sph, mul_one]
    have h1 : (0 : ℝ) ≤ 1 - (p.1 : ℝ) := by linarith [p.1.2.2]
    rw [abs_of_nonneg h1]
    linarith [p.1.2.1]
  -- the continuous shrinking `𝕀 × 𝕊ʲ → 𝔻ʲ⁺¹`
  let ψ : C(unitInterval × Sph j, Ball (j + 1)) :=
    ⟨fun p => ⟨(1 - ((p.1 : unitInterval) : ℝ)) •
        ((p.2 : Sph j) : EuclideanSpace ℝ (Fin (j + 1))), hmem p⟩,
      Continuous.subtype_mk (by fun_prop) hmem⟩
  -- the induced null-homotopy of `g`
  let Kc : C(unitInterval × Sph j, Y) := g.comp ψ
  -- `f₁` is null-homotopic: shrink the sphere linearly to the centre of the disc
  have Hnull : f₁.Homotopy (ContinuousMap.const (Sph j) (g c)) := by
    refine ContinuousMap.Homotopy.mk (toContinuousMap := Kc) ?_ ?_
    · intro x
      show g (ψ (0, x)) = f₁ x
      have hψ : (ψ (0, x) : Ball (j + 1)) =
          ⟨x.1, Metric.sphere_subset_closedBall x.2⟩ := by
        apply Subtype.ext
        simp [ψ]
      rw [hψ]
      exact hg x
    · intro x
      show g (ψ (1, x)) = g c
      have hψ : (ψ (1, x) : Ball (j + 1)) = c := by
        apply Subtype.ext
        simp [ψ, c]
      rw [hψ]
  -- hence `f₀`, being homotopic to `f₁`, is null-homotopic too
  have hconst : f₀.Homotopic (ContinuousMap.const (Sph j) (g c)) := h.trans ⟨Hnull⟩
  -- and a null-homotopic sphere map extends over the disc
  obtain ⟨G, hG⟩ :=
    Work.Conn.Extend.exists_continuousMap_ball_of_homotopic_const f₀ (g c) hconst
  refine ⟨G, ?_⟩
  intro x
  have hx : G (SphToBall j x) = f₀ x := by
    have h1 := ContinuousMap.congr_fun hG x
    simpa only [ContinuousMap.coe_comp, Function.comp_apply] using h1
  rw [show SphToBall j x = ⟨x.1, Metric.sphere_subset_closedBall x.2⟩ from
    Subtype.ext rfl] at hx
  exact hx

end Work.Geo.Radial
